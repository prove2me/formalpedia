-- Prove2me | Theorems.Thm_SharpConsist_lemma_5_2
-- name    : SharpConsist.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:13:53.655818+00:00
-- url     : https://prove2.me/theorems/e54c9f20-22f3-4eca-8eee-a009943fa230
-- title:
--   Lemma 5.2 (i)–(iv) — exact hiding with a legal future
-- statement:
--   Fix $T\in[7/5,3/2]$ and an integer $m\ge32$, integers $k\ge1$ and $n=(m+1)k$, $\delta=1/(64m)$, and a $k$-set $A\subseteq X=[n]$.
--
--   1. **(i) Exact hiding.** $\psi$ is nondecreasing and concave on $[0,m+1]$ with $\psi(0)=0$, and for every $S\subseteq X$ with $|u_A(S)|\le\delta$, $f_A(S)=\psi(|S|/k)$.
--   2. **(ii) Final-arrival compatibility.** $f_A$ is normalized, monotone and submodular on all subsets of $X\cup\{r\}$.
--   3. **(iii) Small marginals.** Every coordinate derivative of $F_\delta$ and $K_\delta$ on $[0,1]\times[0,m]$ lies in $[0,5]$; and for every $e\in X$ and $U\subseteq(X\cup\{r\})\setminus\{e\}$, $0\le f_A(U\cup\{e\})-f_A(U)\le5/k$.
--   4. **(iv) Value gap.**
--   $$K_\delta\Bigl(\tfrac1{m+1},\tfrac m{m+1}\Bigr)=R(T)+\phi_m(1)+32\delta e^{-1}\le R(T)+\frac{32}m+32\delta,$$
--   $$K_\delta(1,0)=1+\phi_m(1)+32\delta e^{-1}\ge1.$$
--
--   The lemma collects the properties of the construction used in the proof of Theorem 5.1: hiding before $r$, legality after $r$, and the gap between the balanced value $R(T)$ and the hidden value $1$.
--
--   Differences from the source:
--   - encoding: X = [n] and the ground set X ∪ {r} → Fin n, embedded in Fin (n+1) by Fin.castSucc, with r = Fin.last n; reason: 0-based indices; same instances
--   - encoding: monotone: f(i | S) ≥ 0; submodular: f(i | S) ≥ f(i | T) for S ⊆ T → PolyContract.IsRankFunction: f(S ∪ T) + f(S ∩ T) ≤ f S + f T, f ∅ = 0, A ⊆ B → f A ≤ f B; reason: equivalent forms on a finite ground set
--   - encoding: partial derivatives ∂_x, ∂_y of the profiles → fderiv ℝ of the profile on ℝ × ℝ applied to (1, 0) or (0, 1); reason: the profiles are C¹ near the rectangle (Lemma B.1(b)), so these are the genuine partials
--   - reading: "Every coordinate derivative of F_δ and K_δ lies in [0, 5]" → for every point of the rectangle [0, 1] × [0, m]; reason: the profiles are constructed and analysed on the count rectangle (§5.1, Lemma B.1); no bound off it is claimed
--   - encoding: ψ defined on [0, m+1] → psi defined on ℝ; monotonicity and concavity stated on [0, m+1]; reason: same claims on the source's domain
--   - encoding: v, w defined on [0, ∞) → v, w defined on ℝ by the quadratic/linear piece for t ≤ T; reason: every argument the statement evaluates is nonnegative (t = ω_m y ≥ 0, z between t and s ≥ 0)
-- source:
--   Fu–Zhang–Tao, A Sharp Barrier of Consistent Submodular Maximization, arXiv:2609.09986 (held version, sha256 874ec76c…), §5.2, Lemma 5.2, p.15

import Mathlib
import Definitions.Def_SharpConsist_fA
import Definitions.Def_SharpConsist_psi
import Definitions.Def_SharpConsist_uA
import Definitions.Def_SharpConsist_RT
import Definitions.Def_PolyContract_IsRankFunction

namespace SharpConsist

/-- **Lemma 5.2 (exact hiding with a legal future), parts (i)–(iv).** Fu–Zhang–Tao, *A Sharp Barrier of Consistent Submodular Maximization*, arXiv:2609.09986 (held version, sha256 874ec76c…), §5.2, Lemma 5.2,
p.15. Fix `T ∈ [7/5, 3/2]`, integers `m ≥ 32`, `k ≥ 1`, `n = (m+1)k`, and a `k`-set `A ⊆ X`.
(i) `ψ` is nondecreasing and concave on `[0, m+1]` with `ψ(0) = 0`, and `f_A(S) = ψ(|S|/k)` for
every `S ⊆ X` with `|u_A(S)| ≤ δ`.
(ii) `f_A` is normalized, monotone and submodular on all subsets of `X ∪ {r}`.
(iii) Every coordinate derivative of `F_δ` and `K_δ` on `[0, 1] × [0, m]` lies in `[0, 5]`, and
`0 ≤ f_A(U ∪ {e}) − f_A(U) ≤ 5/k` for every `e ∈ X` and `U ⊆ (X ∪ {r}) \ {e}`.
(iv) `K_δ(1/(m+1), m/(m+1)) = R(T) + ϕ_m(1) + 32δe^{−1} ≤ R(T) + 32/m + 32δ` and
`K_δ(1, 0) = 1 + ϕ_m(1) + 32δe^{−1} ≥ 1`. -/
theorem lemma_5_2 (T : ℝ) (hT : T ∈ Set.Icc (7 / 5 : ℝ) (3 / 2)) (m k n : ℕ) (hm : 32 ≤ m)
    (hk : 1 ≤ k) (hn : n = (m + 1) * k) (A : Finset (Fin n)) (hA : A.card = k) :
    -- (i)
    (MonotoneOn (psi T m) (Set.Icc 0 ((m : ℝ) + 1)) ∧
      ConcaveOn ℝ (Set.Icc 0 ((m : ℝ) + 1)) (psi T m) ∧ psi T m 0 = 0 ∧
      ∀ S : Finset (Fin n), |uA k m A S| ≤ deltaM m →
        fA T m k A (embedX S) = psi T m ((S.card : ℝ) / (k : ℝ))) ∧
    -- (ii)
    PolyContract.IsRankFunction (fA T m k A) ∧
    -- (iii)
    ((∀ p ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) m, ∀ e ∈ ({(1, 0), (0, 1)} : Set (ℝ × ℝ)),
        fderiv ℝ (fun q : ℝ × ℝ => Fdelta T m q.1 q.2) p e ∈ Set.Icc (0 : ℝ) 5 ∧
        fderiv ℝ (fun q : ℝ × ℝ => Kdelta T m q.1 q.2) p e ∈ Set.Icc (0 : ℝ) 5) ∧
      ∀ (e : Fin n) (U : Finset (Fin (n + 1))), Fin.castSucc e ∉ U →
        0 ≤ fA T m k A (insert (Fin.castSucc e) U) - fA T m k A U ∧
        fA T m k A (insert (Fin.castSucc e) U) - fA T m k A U ≤ 5 / (k : ℝ)) ∧
    -- (iv)
    (Kdelta T m (1 / ((m : ℝ) + 1)) ((m : ℝ) / ((m : ℝ) + 1)) =
        RT T + phiM m 1 + 32 * deltaM m * Real.exp (-1) ∧
      RT T + phiM m 1 + 32 * deltaM m * Real.exp (-1) ≤ RT T + 32 / (m : ℝ) + 32 * deltaM m ∧
      Kdelta T m 1 0 = 1 + phiM m 1 + 32 * deltaM m * Real.exp (-1) ∧
      1 ≤ 1 + phiM m 1 + 32 * deltaM m * Real.exp (-1)) := by sorry

end SharpConsist
