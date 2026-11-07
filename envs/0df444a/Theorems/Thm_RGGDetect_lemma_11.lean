-- Prove2me | Theorems.Thm_RGGDetect_lemma_11
-- name    : RGGDetect.lemma_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:40:54.203843+00:00
-- url     : https://prove2.me/theorems/dbfd59cd-71b5-4702-9194-d91160d986b8
-- title:
--   Lemma 11 — $T^{u,S}_{\mathbf a}$ preserves tensor products and contracts $L^2$
-- statement:
--   Let $D\in\mathcal H_{\boldsymbol\ell}$ for $\boldsymbol\ell=(\ell_v:v\in V)$, fix a marked vertex $u\in V$, $h=\ell_u$, and $\mathbf a\in\mathbb N^S$; let $D'=T^{u,S}_{\mathbf a}D$, a function of $x_{V'}$, $V'=(V\setminus u)\cup S$.
--
--   1. (**Preservation of tensor product**) $D'\in\mathcal H_{\boldsymbol\ell'}$ with $\ell'_i=\ell_i$ for $i\in V\setminus\{u\}$ and $\ell'_i=a_i$ for $i\in S$.
--   2. (**Contraction**) Let $\|\mathbf a\|_1\ge h$ and define $b_m$ by $\Phi_{\mathbf a}(t)=\prod_{v\in S}P_{a_v}(t)=\sum_{m\ge0}b_mP_m(t)$. Then, with $q,s$ as in (55),
--   $$
--   \mathbb E((D')^2)=\frac{d^{2q}b_h}{N_{h,d}\prod_{v\in S}N_{a_v,d}}\,\mathbb E(D^2)\le\frac C{d^s}\,\mathbb E(D^2), \tag{115}
--   $$
--   where $C$ depends only on $\|\mathbf a\|_1$ and $h$.
--
--   Furthermore, both parts apply to $D\equiv1$ with $V=\{u\}$ and $h=0$, in which case $V'=S$ and $D'\in\mathcal H_{\mathbf a}$.
--
--   This is what lets the cavity recurrence stay inside the family of tensor-product harmonics.
--
--   **Formalization Note** $S$ is disjoint from $V$, $a_i\ge1$ on $S$, $d\ge2$; $b_h$ is computed by (127). The constant is chosen after $\|\mathbf a\|_1$ and $h$ and before everything else.
--
--   Differences from the source:
--   - encoding: Lemma 11 for the paper's d → d ≥ 2; reason: P_{ℓ,d} is defined only for d ≥ 2
--   - encoding: b_h defined by the expansion Φ_a = Σ b_m P_m → b_h = N_h E_ρ[P_h(ρ) Φ_a(ρ)]; reason: the paper's identity (127), from the orthogonality (124)
--   - encoding: S ⊆ V^c, a ∈ ℕ^S → S disjoint from V, a positive on S (values off S unused); reason: indexing; (60) takes S ⊆ V^c
-- source:
--   Du, Mao, Sun, Wu, Xu, Sharp detection thresholds for random geometric graphs with polynomial average degrees, arXiv:2610.08517 (held version, sha256 e7bebd4a…), Lemma 11, eq. (115), p.31 (PDF p.33)

import Mathlib
import Definitions.Def_RGGDetect_harmCoef

open MeasureTheory

namespace RGGDetect

/-- **Lemma 11** (the averaging operator; arXiv:2610.08517, held version, sha256 e7bebd4a…, Lemma 11,
p.31, eq. (115)): let `D ∈ H_ℓ`, `ℓ = (ℓ_v : v ∈ V)`, fix `u ∈ V`, `h = ℓ_u`, `a ∈ ℕ^S`, and
`D′ = T^{u,S}_a D`, `V′ = (V ∖ u) ∪ S`. Then
1. (preservation of tensor product) `D′ ∈ H_{ℓ′}`, `ℓ′_i = ℓ_i` on `V ∖ {u}` and `a_i` on `S`;
2. (contraction) if `‖a‖₁ ≥ h`, with `Φ_a(t) = ∏_{v∈S} P_{a_v}(t) = ∑_m b_m P_m(t)`,
   `E((D′)²) = d^{2q} b_h/(N_{h,d} ∏_{v∈S} N_{a_v,d}) E(D²) ≤ (C/d^s) E(D²)`,
   `C` depending only on `‖a‖₁` and `h`.
Furthermore both parts apply to `D ≡ 1` with `V = {u}` and `h = 0`, in which case `V′ = S` and
`D′ ∈ H_a`.

**Formalization Note** Configurations of `n` points; `S` is disjoint from `V` (the operator (60) takes
`S ⊆ V^c`); `a` is positive on `S` and its values off `S` are irrelevant. `b_h` is `bCoef` (127),
`q = (h + ‖a‖₁)/2`, `s = (‖a‖₁ - h)/2` as reals. `d ≥ 2`, where `P_{ℓ,d}` is defined. The constant is
chosen after `‖a‖₁ = A` and `h`, before everything else. -/
theorem lemma_11 :
    (∀ n d : ℕ, 2 ≤ d → ∀ (V : Finset (Fin n)) (ℓ : Fin n → ℕ), (∀ v ∈ V, 1 ≤ ℓ v) →
      ∀ D : Config n d → ℝ, D ∈ tensorHarm V ℓ → ∀ u ∈ V, ∀ S : Finset (Fin n), Disjoint S V →
      ∀ a : Fin n → ℕ, (∀ i ∈ S, 1 ≤ a i) →
        opT d (ℓ u) u S a D ∈ tensorHarm (V.erase u ∪ S) (fun i => if i ∈ S then a i else ℓ i)) ∧
    (∀ A h : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ n d : ℕ, 2 ≤ d → ∀ (V : Finset (Fin n)) (ℓ : Fin n → ℕ),
      (∀ v ∈ V, 1 ≤ ℓ v) → ∀ D : Config n d → ℝ, D ∈ tensorHarm V ℓ → ∀ u ∈ V, ℓ u = h →
      ∀ S : Finset (Fin n), Disjoint S V → ∀ a : Fin n → ℕ, (∀ i ∈ S, 1 ≤ a i) →
      ∑ i ∈ S, a i = A → h ≤ A →
        ∫ x, opT d h u S a D x ^ 2 ∂(prior n d) =
            (d : ℝ) ^ (2 * qHA h S a) * bCoef d h S a /
              ((harmDim d h : ℝ) * ∏ v ∈ S, (harmDim d (a v) : ℝ)) * ∫ x, D x ^ 2 ∂(prior n d) ∧
        ∫ x, opT d h u S a D x ^ 2 ∂(prior n d) ≤
            C / (d : ℝ) ^ (((A : ℝ) - h) / 2) * ∫ x, D x ^ 2 ∂(prior n d)) ∧
    (∀ n d : ℕ, 2 ≤ d → ∀ (u : Fin n) (S : Finset (Fin n)), u ∉ S → ∀ a : Fin n → ℕ,
      (∀ i ∈ S, 1 ≤ a i) → opT d 0 u S a (fun _ => (1 : ℝ)) ∈ tensorHarm S a) ∧
    (∀ A : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ n d : ℕ, 2 ≤ d → ∀ (u : Fin n) (S : Finset (Fin n)), u ∉ S →
      ∀ a : Fin n → ℕ, (∀ i ∈ S, 1 ≤ a i) → ∑ i ∈ S, a i = A →
        ∫ x, opT d 0 u S a (fun _ => (1 : ℝ)) x ^ 2 ∂(prior n d) =
            (d : ℝ) ^ (2 * qHA 0 S a) * bCoef d 0 S a /
              ((harmDim d 0 : ℝ) * ∏ v ∈ S, (harmDim d (a v) : ℝ)) *
              ∫ _x, (1 : ℝ) ^ 2 ∂(prior n d) ∧
        ∫ x, opT d 0 u S a (fun _ => (1 : ℝ)) x ^ 2 ∂(prior n d) ≤
            C / (d : ℝ) ^ ((A : ℝ) / 2) * ∫ _x, (1 : ℝ) ^ 2 ∂(prior n d)) := by sorry

end RGGDetect
