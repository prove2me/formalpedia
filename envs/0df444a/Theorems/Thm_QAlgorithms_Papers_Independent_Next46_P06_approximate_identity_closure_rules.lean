-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P06_approximate_identity_closure_rules
-- name    : QAlgorithms.Papers.Independent.Next46.P06.approximate_identity_closure_rules
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:43:39.722993+00:00
-- url     : https://prove2.me/theorems/750cfb08-fd94-4d45-9b84-0ae8ec6fc436
-- title:
--   Theorem 7.2
-- statement:
--   Let $F$ be a commutative unital complex algebra and $\Phi:F\to\mathcal C(X)$ a proto-calculus on a complex Banach space. Let $f,g\in F$. A common weak approximate identity $(e_n)$ for $f,g$ is also a weak approximate identity for $f+g$ and every $\lambda f$, and
--
--   $$\overline{\Phi(f)+\Phi(g)}=\Phi(f+g).$$
--
--   The same preservation holds for strong approximate identities. In that case $(e_n^2)$ is a strong approximate identity for $fg$, and
--
--   $$\overline{\Phi(f)\Phi(g)}=\Phi(fg).$$
--
--   Closures are graph closures. The printed bounded codomain is corrected to the section's closed-operator codomain, preserving the unbounded assertion; this correction requires independent moderation.
-- source:
--   On the Fundamental Principles of Unbounded Functional Calculi, arXiv:2009.04733v1, PDF p. 19, Theorem 7.2

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P06

noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter

open scoped Topology

namespace QAlgorithms.Papers.Independent.Next46.P06

open QAlgorithms.Papers.Independent.Claimed50.P05 (graphDomain GraphCore)

universe u v w

variable {F G : Type*} [Ring F] [Algebra ℂ F] [Ring G] [Algebra ℂ G]

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]

/-- Theorem 7.2, PDF p.19: graph closures of the sum and product. Printed:
codomain L(X). Changed: C(X), consistent with the section, the unbounded proof
and its closure conclusions. Why: retaining L(X) would drop the intended
unbounded assertion. Commutativity comes from p.18. Independent moderation
must review this correction. -/
theorem approximate_identity_closure_rules [CompleteSpace X] (Phi : F → Graph X) (hPhi : Proto Phi)
    (hcomm : ∀ f g : F, f * g = g * f) (f g : F) (e : ℕ → F) :
    (WeakApprox Phi e f → WeakApprox Phi e g →
      WeakApprox Phi e (f + g) ∧ (∀ c : ℂ, WeakApprox Phi e (c • f)) ∧
      closure (graphAdd (Phi f) (Phi g)) = Phi (f + g)) ∧
    (StrongApprox Phi e f → StrongApprox Phi e g →
      StrongApprox Phi e (f + g) ∧ (∀ c : ℂ, StrongApprox Phi e (c • f)) ∧
      closure (graphAdd (Phi f) (Phi g)) = Phi (f + g) ∧
      StrongApprox Phi (fun n => e n * e n) (f * g) ∧
      closure (graphMul (Phi f) (Phi g)) = Phi (f * g)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P06

end
