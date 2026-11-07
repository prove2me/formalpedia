-- Prove2me | Theorems.Thm_PairwiseRealize_sec_A_2_node_rounding
-- name    : PairwiseRealize.sec_A_2_node_rounding
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:56:43.901339+00:00
-- url     : https://prove2.me/theorems/b7538615-8ebd-44b8-b4f6-3f2f53fbca8e
-- title:
--   §A.2, p.12 — rounding at a node: signed residual at most $u_d=160000\lceil\sqrt{4d}\rceil$, and integral
-- statement:
--   Let $A,B$ be disjoint nonempty coordinate groups, $d=|A||B|$, let $(u_a,v_a,w_a,z_a)_{a<k}$ be bundles with change vectors $g_a$, let $q^0\in\{0,1\}^k$, and let $p\in[0,1]^k$ be rational with at most $d$ entries outside $\{0,1\}$. Then there is $q\in\{0,1\}^k$, equal to $p$ wherever $p$ is $0$ or $1$, with
--
--   $$\Bigl|\sum_ag_a(i,j)(q_a-p_a)\Bigr|\le160000\lceil\sqrt{4d}\rceil\quad\text{for every }(i,j)\in A\times B.$$
--
--   Moreover, if $\sum_a(p_a-q^0_a)g_a$ is integral, then so is the residual $\sum_a(p_a-q_a)g_a$.
--
--   This is the residual a node passes to its two children.
--
--   Differences from the source:
--   - generalization: accepted rectangular bundles of a node → any tuples (uₐ, vₐ, wₐ, zₐ), not necessarily distinct strings; reason: the bound uses only the four binary product matrices
-- source:
--   Shi, Sun, Robust Exact Realization of Pairwise Boolean Statistics, STOC 2027 submission (sha256 62090516…), §A.2, p.12 (PDF p.13); §3.2, p.7 (PDF p.8)

import Mathlib
import Definitions.Def_PairwiseRealize_Bundles

namespace PairwiseRealize

/-- **Rounding at a node, §A.2 p.12 (PDF p.13); §3.2 p.7 (PDF p.8).** K. Shi, H. Sun, *Robust Exact
Realization of Pairwise Boolean Statistics*, STOC 2027 submission (manuscript sha256 62090516…):
"Stack the four binary product matrices UᵢWⱼ, UᵢZⱼ, VᵢWⱼ, VᵢZⱼ, giving 4d_R constraints. Apply
Theorem C.1 to the at most d_R fractional exchange variables in a basic solution. The resulting
signed residual is at most u_{d_R} in each coordinate. The residual is integral, even though the four
block targets individually need not be integral." Here `u_d = 160000⌈√(4d)⌉` (p.11).

Let `A, B` be disjoint nonempty coordinate groups, `d = |A||B|`, `(uₐ, vₐ, wₐ, zₐ)_{a<k}` rectangular
bundles with change vectors `gₐ`, `q⁰ ∈ {0,1}^k` a baseline, and `p ∈ [0,1]^k` rational with at most
`d` entries outside `{0, 1}`. Then there is `q ∈ {0,1}^k`, equal to `p` wherever `p` is `0` or `1`,
with `|Σₐ gₐ(i,j)(qₐ − pₐ)| ≤ 160000⌈√(4d)⌉` for every `(i, j) ∈ A × B`; and if
`Σₐ (pₐ − q⁰ₐ) gₐ` is integral, so is the residual `Σₐ (pₐ − qₐ) gₐ`. -/
theorem sec_A_2_node_rounding (n : ℕ) (A B : Finset (Fin n)) (hAB : Disjoint A B)
    (hA : A.Nonempty) (hB : B.Nonempty) (k : ℕ) (c : Fin k → BundleData n A B)
    (q0 : Fin k → Bool) (p : Fin k → ℚ) (hp : ∀ a, 0 ≤ p a ∧ p a ≤ 1)
    (hfrac : (Finset.univ.filter fun a => p a ≠ 0 ∧ p a ≠ 1).card ≤ A.card * B.card) :
    ∃ q : Fin k → Bool, (∀ a, (p a = 0 ∨ p a = 1) → (bv (q a) : ℚ) = p a) ∧
      (∀ ij : A × B, |∑ a, (gvec (c a)).ofLp ij * ((bv (q a) : ℝ) - p a)| ≤
        160000 * (⌈Real.sqrt (4 * (A.card * B.card : ℕ))⌉₊ : ℝ)) ∧
      ((∀ ij : A × B, ∃ z : ℤ, ∑ a, ((p a : ℝ) - bitR (q0 a)) * (gvec (c a)).ofLp ij = z) →
        ∀ ij : A × B, ∃ z : ℤ, ∑ a, ((p a : ℝ) - bitR (q a)) * (gvec (c a)).ofLp ij = z) := by sorry

end PairwiseRealize
