-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P44_choiSDPEquivalence
-- name    : QAlgorithms.Papers.Independent.Information100.P44.choiSDPEquivalence
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:46:29.919194+00:00
-- url     : https://prove2.me/theorems/b8bccf85-6a66-4305-86c2-befc82cb71a2
-- title:
--   V C: equivalence of channel and Choi CGP constraints
-- statement:
--   For the fixed four-level instance, use the output-first unnormalized Choi convention
--   $$J_{(x,u),(y,v)}=\Phi(|u\rangle\langle v|)_{xy},\qquad \Phi(X)_{xy}=\sum_{u,v}J_{(x,u),(y,v)}X_{uv}.$$
--   A channel is feasible for the CGP task if and only if its Choi matrix is positive semidefinite, satisfies $\sum_xJ_{(x,u),(x,v)}=\delta_{uv}$, $\sum_uJ_{(x,u),(y,u)}\gamma_u=\gamma_x\delta_{xy}$, vanishes unless $E_x-E_u=E_y-E_v$, and its reconstructed output on the fixed input has coarse populations $(1/2,7/20,3/20)$. Conversely every matrix satisfying these constraints reconstructs a feasible channel and is exactly its Choi matrix. This is the concrete SDP equivalence, including both reconstruction identities and no input transpose.
-- source:
--   Limitations on Joint Coherence Transfer in Quantum Thermodynamics, arXiv:2608.11872v1, PDF p. 16, V C: equivalence of channel and Choi CGP constraints

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44

namespace QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- PDF pp.16–17, V C: both channel-to-Choi and Choi-to-channel directions of the exact SDP. -/
theorem choiSDPEquivalence :
    (∀ Phi : Map 4, FixedChannelFeasible Phi ↔
      FixedChoiFeasible (choi Phi) ∧ ∀ X, fromChoi (choi Phi) X = Phi X) ∧
    (∀ J : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ,
      FixedChoiFeasible J ↔ FixedChannelFeasible (fromChoi J) ∧ choi (fromChoi J) = J) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P44
