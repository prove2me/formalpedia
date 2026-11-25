-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_PBN_chainX1__26f16dba7621
-- name    : P2M_Formalism_FourierDecayAlt_P_PBN_chainX1__26f16dba7621
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:17:25.544867+00:00
-- url     : https://prove2.me/theorems/db335535-fb37-5ba4-84b9-e14fde8781af
-- title:
--   P2 M Formalism Fourier Decay Alt P PBN chain X1  26f16dba7621: P2 M Formalism Fourier Decay Alt P PBN chain X1  26f16dba7621
-- statement:
--   The P2 M Formalism Fourier Decay Alt P PBN chain X1  26f16dba7621 construction uses the P2 M Formalism Fourier Decay Alt P PBN chain X1  26f16dba7621 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainX1.lean#L9-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainX1.lean#L9-L115

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainFirstIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainX1
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBN
open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.SignAntidiagonal

theorem P2M_Formalism_FourierDecayAlt_P_PBN_chainX1__26f16dba7621 {A M : Type} [Ring A] [Algebra ℂ A] [AddCommGroup M] [Module ℂ M] (k r : ℕ) (c : Fin r → ℂ)
    (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (La : A →ₗ[ℂ] M) (hG : GlRel E) (m : ℕ) (hm : m + 2 ≤ r)
    (u : ℂ)
    (hR0 : ∀ (x : A) (l : ℕ) (hl : l < m), La (x * E (eI k r ⟨l, by omega⟩) (eI k r ⟨m + 1, by omega⟩)) = 0)
    (hR1 : ∀ x : A, La (x * E (eI k r ⟨m, by omega⟩) (eI k r ⟨m + 1, by omega⟩)) = La x)
    (hL : ∀ (x : A) (q : ℕ) (hq : q ≤ m), La (E (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨q, by omega⟩) * x) =
      (if q = m then c ⟨m + 1, by omega⟩ / c ⟨m, by omega⟩ else 0) • La x) :
    La (qminor E (xR k r (m + 2) hm) (xR k r (m + 2) hm) u) =
      La (qminor E (xR k r (m + 1) (by omega)) (xR k r (m + 1) (by omega)) u *
          Tm E (u - ((m + 1 : ℕ) : ℂ)) (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨m + 1, by omega⟩)) -
        (c ⟨m + 1, by omega⟩ / c ⟨m, by omega⟩) • La (qminor E (xR k r m (by omega)) (xR k r m (by omega)) u) := by sorry

alias «Formalism».«FourierDecayAlt».«P».«PBN».«chainX1'» := P2M_Formalism_FourierDecayAlt_P_PBN_chainX1__26f16dba7621
