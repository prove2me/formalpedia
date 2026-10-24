-- Prove2me | Theorems.Thm_PandoraBO_Private20261023_coordinate_nonanticipative_factorization
-- name    : PandoraBO.Private20261023.coordinate_nonanticipative_factorization
-- status  : Proved
-- author  : @QianJaneXie
-- created : 2026-10-24T01:17:36.022133+00:00
-- url     : https://prove2.me/theorems/2656bf5a-1112-42c1-bbf3-9bba0c0b408a
-- title:
--   Nonanticipative functions factor from a box reward in expectation
-- statement:
--   If changing one box reward while fixing the other rewards and the policy seed leaves a function unchanged, its product with a function of that reward has factorized expectation under the independent reward and seed law.
-- source:
--   Auxiliary finite-product integration lemma for the capped-reward proof of Weitzman optimality in the Pandora model.

import Definitions.Def_PandoraBO_Model
open MeasureTheory
set_option autoImplicit false

theorem PandoraBO.Private20261023.coordinate_nonanticipative_factorization {n : ℕ} (M : PandoraBO.Instance n) (i : PandoraBO.Box n)
    (a : PandoraBO.Outcome n → ℝ) (g : ℝ → ℝ)
    (ha : ∀ (r r' : PandoraBO.Box n → ℝ) (u : ℝ),
      (∀ j, j ≠ i → r j = r' j) → a (r, u) = a (r', u)) :
    (∫ ω : PandoraBO.Outcome n, a ω * g (ω.1 i) ∂PandoraBO.jointLaw M) =
      (∫ ω : PandoraBO.Outcome n, a ω ∂PandoraBO.jointLaw M) *
        (∫ y : ℝ, g y ∂M.law i) := by sorry
