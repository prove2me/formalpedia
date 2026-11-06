-- Prove2me | Theorems.Thm_SparsificationLemma_Mach_Cert_round_eq
-- name    : SparsificationLemma.Mach.Cert.round_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:05:20.284416+00:00
-- url     : https://prove2.me/theorems/0896aa28-a074-4253-8ce1-018fee53e896
-- title:
--   Cert: round eq
-- statement:
--   `round` with its case distinctions written by eliminators.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Mach/Cert.lean#L32-L38
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Mach/Cert.lean#L32-L38

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Mach_Walk
import Definitions.Def_UniformInK_Cert_Walk
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Definitions.Def_SparsificationLemma_Mach_Cert
import Theorems.Thm_Groundwork_PolyT_elim
import Theorems.Thm_WidthK_InvK_step

set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Mach SparsificationLemma.Mach.Cert
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSat.Poly CountKSatRate CountKSatRate.Cert UniformInK PaddedDescent PaddedDescent.F ClauseBound.Alg
variable {α σ : Type} [Enc α]
omit [Enc α]

theorem SparsificationLemma.Mach.Cert.round_eq (step : σ → Option (σ × σ)) (st : List σ × List σ) :
    Sparsify.round step st = st.1.head?.elim ([], st.2) fun s =>
      (step s).elim (st.1.tail, s :: st.2) fun lh => (lh.1 :: lh.2 :: st.1.tail, st.2) := by sorry
