-- Prove2me | Theorems.Thm_RGGDetect_proposition_3
-- name    : RGGDetect.proposition_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:39:44.277414+00:00
-- url     : https://prove2.me/theorems/29b8de96-d1fa-474b-b2c9-7370729911d8
-- title:
--   Proposition 3 — weighted high-frequency Fourier tail $\le\mathbb E(D^2)B_{m,K,r}$
-- statement:
--   Let $m\le n$, $h\ge0$ and $V\subseteq[n]\setminus[m]$, and let $D(z,X_V)$ be a spherical harmonic in the variables $z$ and $X_V=\{x_v:v\in V\}$ with degree $h$ in $z$ (when $h=0$, $V=\varnothing$ and $D\equiv1$ are allowed). Let $\eta_{D,S}=\mathbb E_z[D(z,X_V)\prod_{j\in S}\kappa(\langle z,x_j\rangle)]$ (102). If $\mathcal F$ is any sub-$\sigma$-field of $\sigma(X_V,X_{[m]})$, then
--
--   $$
--   \mathbb E_{\mathcal F}\Bigg[\int_{T_{m,r}}\Big(\sum_{S\subseteq[m],\,|S|\ge K}\mathbb E(\eta_{D,S}\mid\mathcal F)\,\psi_S(y)\Big)^2dQ_m(y)\Bigg]\le\mathbb E(D^2)\,B_{m,K,r}.
--   $$
--
--   It controls the high-frequency part of the Fourier expansion of the row likelihood (Theorem 3) and of the cavity numerator (Lemma 7) on the typical-degree set $T_{m,r}$.
--
--   **Formalization Note** The $n+1$ points $z,x_1,\dots,x_n$ are indexed by `Fin (n+1)`, $z$ last; $[m]$ is the first $m$ indices. $D$ lies in the tensor space on $V\cup\{z\}$ with degree $h$ at $z$. The conditional expectation is Mathlib's `condExp`. $d\ge1$, $0<p<1$; $K,r$ arbitrary.
--
--   Differences from the source:
--   - generalization: D a spherical harmonic with degree h in z; when h = 0, V = ∅ and D ≡ 1 allowed → any h ≥ 0, any V ⊆ [n]∖[m] and any D in the tensor space on V ∪ {z} with degree h at z (a degree-0 factor is a constant); reason: contains the paper's cases (h ≥ 1, and h = 0 with V = ∅, D ≡ 1); the proof, via (104)–(106), uses only that D is harmonic of degree h in z
--   - encoding: z, x_1, …, x_n and S ⊆ [m] → n + 1 points on Fin (n+1) with z the last index; S a subset of Fin m embedded into Fin (n+1); reason: indexing
--   - encoding: E_F[…] and E(η_{D,S} | F) → the prior expectation of an expression in Mathlib's condExp for a sub-σ-algebra F ≤ σ(X_V, X_[m]); reason: Lean convention; same instances
-- source:
--   Du, Mao, Sun, Wu, Xu, Sharp detection thresholds for random geometric graphs with polynomial average degrees, arXiv:2610.08517 (held version, sha256 e7bebd4a…), Proposition 3, eq. (103), p.26 (PDF p.28)

import Mathlib
import Definitions.Def_RGGDetect_cavity
import Definitions.Def_RGGDetect_harmPoly
import Definitions.Def_RGGDetect_fourierTail

open MeasureTheory
open scoped Classical

namespace RGGDetect

/-- **Proposition 3** (weighted high-frequency tail; arXiv:2610.08517, held version, sha256 e7bebd4a…,
Proposition 3, p.26, eq. (103)): for `m ≤ n`, `h ≥ 0` and `V ⊆ [n] ∖ [m]`, let `D(z, X_V)` be a
spherical harmonic in `z` and `X_V` with degree `h` in `z`. If `F` is any sub-σ-field of
`σ(X_V, X_{[m]})`, then
`E_F[∫_{T_{m,r}} (∑_{S ⊆ [m], |S| ≥ K} E(η_{D,S} | F) ψ_S(y))² dQ_m(y)] ≤ E(D²) B_{m,K,r}`.

**Formalization Note** The `n + 1` points are indexed by `Fin (n + 1)`: `z` is the last index `n`, the
paper's `x₁, …, x_m` are the indices `0, …, m - 1`, and `V` lies in `{m, …, n - 1}`. `D` lies in the
tensor space `H_ℓ` on `V ∪ {z}` with `ℓ_z = h` (`h = 0` gives a constant in `z`, so `V = ∅`, `D ≡ 1` is
included). A subset `S ⊆ [m]` is a `Finset (Fin m)`, embedded into `Fin (n + 1)` for `η_{D,S}`. The
conditional expectation is Mathlib's `condExp` given `F ≤ σ(X_V, X_{[m]})`; the outer `E_F` is the
expectation under the prior. `0 < p < 1` with `p = capProb d τ`, `d ≥ 1`; `K, r` arbitrary. -/
theorem proposition_3 (n d : ℕ) (hd : 1 ≤ d) (τ : ℝ) (hp0 : 0 < capProb d τ)
    (hp1 : capProb d τ < 1) (m : ℕ) (hm : m ≤ n) (h : ℕ) (V : Finset (Fin (n + 1)))
    (hV : ∀ v ∈ V, m ≤ v.val ∧ v.val < n) (ℓ : Fin (n + 1) → ℕ) (hℓ : ∀ v ∈ V, 1 ≤ ℓ v)
    (hℓz : ℓ (Fin.last n) = h) (D : Config (n + 1) d → ℝ)
    (hD : D ∈ tensorHarm (insert (Fin.last n) V) ℓ)
    (F : MeasurableSpace (Config (n + 1) d))
    (hF : F ≤ MeasurableSpace.comap
      (fun x : Config (n + 1) d => fun i : {i : Fin (n + 1) // i ∈ V ∨ i.val < m} => x i.1)
      MeasurableSpace.pi)
    (K r : ℕ) :
    ∫ x, ∑ y : Fin m → Bool,
        (if y ∈ Tmr m r then
          (∑ S ∈ (Finset.univ : Finset (Finset (Fin m))).filter (fun S => K ≤ S.card),
            condExp F (prior (n + 1) d)
              (etaDS d τ D (Fin.last n) (S.map (Fin.castLEEmb (by omega)))) x *
              psi (capProb d τ) S y) ^ 2 * bernProd (capProb d τ) y
        else 0) ∂(prior (n + 1) d) ≤
      (∫ x, D x ^ 2 ∂(prior (n + 1) d)) * Btail d τ m K r := by sorry

end RGGDetect
