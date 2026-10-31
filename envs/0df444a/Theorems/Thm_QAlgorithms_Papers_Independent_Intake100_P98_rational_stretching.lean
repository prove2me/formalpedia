-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P98_rational_stretching
-- name    : QAlgorithms.Papers.Independent.Intake100.P98.rational_stretching
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:08:07.335055+00:00
-- url     : https://prove2.me/theorems/8afd2bd2-0cfb-41e2-8bd2-b1caf813d8b2
-- title:
--   Corollary 4.2: rational polynomial stretching
-- statement:
--   Let $k\ge1$. A partition is a weakly decreasing $k$-tuple of nonnegative integers, padded by zeros. Let x=(λ,µ,ν) be any such partition triple, including triples with unequal sizes or failed containment. Write $c^\nu_{\lambda\mu}$ for the ordinary homogeneous Littlewood–Richardson coefficient.
--
--   For each fixed triple there exists $p_x\in\mathbb Q[N]$, chosen independently of the positive integer $N$, such that
--
--   $$
--   p_x(N)=c^{N\nu}_{N\lambda\,N\mu}\quad(N\ge1),\qquad
--   \deg p_x\le3{k-1\choose2}.
--   $$
--
--   This is polynomial stretching on a fixed ray. It does not assert nonnegative polynomial coefficients, an exact degree, or agreement at zero for unsupported triples.
-- source:
--   A polynomiality property for Littlewood-Richardson coefficients, arXiv:math/0308101v2, PDF p. 10, Corollary 4.2: rational polynomial stretching

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P98

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P98

open QAlgorithms.Papers.Independent.Frontier30.P19

attribute [local instance] Classical.propDecidable

/-- Corollary 4.2, PDF p.10. N is positive, as in Conjecture 1.1 (p.2).
The polynomial is chosen after the triple and before N. Unsupported triples may
have the zero polynomial; no constant term or coefficient positivity is claimed.
All partition triples are included, including unequal sizes and noncontainment. -/
theorem rational_stretching (k : ℕ) (hk : 0 < k)
    (x : Coordinates k → ℕ) (hx : ∀ b : Fin 3, Antitone (fun i => x (b,i))) :
    ∃ p : Polynomial ℚ, p.natDegree ≤ 3 * Nat.choose (k-1) 2 ∧
      ∀ N : ℕ, 0 < N → p.eval (N : ℚ) = (paddedLRCoefficient (stretch x N) : ℚ) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P98

end
