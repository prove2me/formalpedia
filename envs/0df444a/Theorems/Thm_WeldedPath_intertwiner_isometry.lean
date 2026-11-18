-- Prove2me | Theorems.Thm_WeldedPath_intertwiner_isometry
-- name    : WeldedPath.intertwiner_isometry
-- status  : Proved
-- author  : @dmilosch
-- created : 2026-11-17T23:49:10.508632+00:00
-- url     : https://prove2.me/theorems/72c3ab8a-9c18-42e3-a4fb-e9b859ddc856
-- title:
--   The canonical completion intertwiner is a degree-preserving isometry
-- statement:
--   For every positive permutation size s, the canonical completion intertwiner I_s has I_s† I_s = 1 and preserves norms. A vector in completion level r is mapped to databases of exactly r records. For every answer encoding and either query direction, the canonical exact compressed oracle intertwines the ordinary permutation query with I_s. All operators are the published canonical ones. No spectral comparison estimate is assumed.
-- source:
--   Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, https://arxiv.org/html/2611.05912v1, equations (10)-(14) and the qualitative isometry/intertwining properties preceding Lemma 2.8. Related: Carolan and Majenz, Compressed Permutation Oracles Revisited, Theorem 4.2 and Lemma 4.10, https://arxiv.org/html/2609.28469v1 . This statement proves the qualitative properties only; it does not assert the quantitative oracle-comparison bounds.

import Definitions.Def_WeldedPath_Supplement_exactCpWT

set_option autoImplicit false
open Classical

namespace WeldedPath

theorem intertwiner_isometry :
    ∀ s : ℕ, 0 < s →
      (ContinuousLinearMap.adjoint (intertwiner s)).comp (intertwiner s) = 1 ∧
      (∀ v : Hil (Equiv.Perm (Fin s)), ‖intertwiner s v‖ = ‖v‖) ∧
      (∀ (r : ℕ) (v : Hil (Equiv.Perm (Fin s))), v ∈ Hlevel s r →
        ∀ I : InjDb s, I.size ≠ r → intertwiner s v I = 0) ∧
      (∀ (d : ℕ) (enc : Fin s → QAlgorithms.Qubits d) (x : Fin s) (inv : Bool),
        (Supplement.exactCpOE enc x inv).comp
          (opTensor (1 : Hil (QAlgorithms.Qubits d) →L[ℂ] Hil (QAlgorithms.Qubits d)) (intertwiner s)) =
        (opTensor (1 : Hil (QAlgorithms.Qubits d) →L[ℂ] Hil (QAlgorithms.Qubits d)) (intertwiner s)).comp
          (Supplement.stdQueryE enc x inv)) := by
  sorry

end WeldedPath
