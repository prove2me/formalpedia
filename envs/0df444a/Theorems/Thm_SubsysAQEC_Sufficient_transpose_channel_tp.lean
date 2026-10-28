-- Prove2me | Theorems.Thm_SubsysAQEC_Sufficient_transpose_channel_tp
-- name    : SubsysAQEC.Sufficient.transpose_channel_tp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:32:13.135335+00:00
-- url     : https://prove2.me/theorems/07d1c133-4081-443b-97f3-e061bafe7210
-- title:
--   (10), p. 3 — the transpose channel R_P is trace preserving on 𝒫_ℰ
-- statement:
--   Let $\mathcal E$ have Kraus operators $E_i:\mathcal H_{AB}\to\mathcal H$, let $\mathcal P_{\mathcal E}$ be the projector onto the support of $\mathcal E(P)=\sum_iE_iE_i^\dagger$, and let $R^P_i=PE_i^\dagger\mathcal E(P)^{-1/2}$ be the Kraus operators of the transpose channel (10), with the inverse square root taken on the support. Then
--
--   $$\sum_i R^{P\,\dagger}_i R^P_i=\mathcal P_{\mathcal E},$$
--
--   so $\mathcal R_P$ is trace preserving on $\mathcal P_{\mathcal E}$ and is an admissible recovery map.
--
--   This is what makes the transpose channel a legitimate candidate recovery in Theorem 2 and Corollary 3, without assuming that $\mathcal E(P)$ has full support.
-- source:
--   Mandayam, Ng, Towards a Unified Framework for Approximate Quantum Error Correction, arXiv:1202.5139v2, p. 3, (10) and the sentence after it

import Mathlib
import Definitions.Def_SubsysAQEC_Sufficient_Setting

namespace SubsysAQEC.Sufficient

open Matrix

theorem transpose_channel_tp {a b o ι : Type} [Fintype a] [Fintype b] [Fintype o] [Fintype ι]
    [DecidableEq a] [DecidableEq b] [DecidableEq o] (E : ι → Matrix o (a × b) ℂ) :
    ∑ i, (transposeKraus E i)ᴴ * transposeKraus E i = outSupport E ∧
      IsRecovery E (transposeKraus E) := by sorry

end SubsysAQEC.Sufficient
