-- Prove2me | Theorems.Thm_PosIndexNash_PPADS_normalForm_enc_injective
-- name    : PosIndexNash.PPADS.normalForm_enc_injective
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:03:18.069295+00:00
-- url     : https://prove2.me/theorems/91c160bf-15af-422b-aca6-3a877eae5411
-- title:
--   The binary encoding of a max-affine normal form is injective
-- statement:
--   The binary code of a normal form determines all of its data uniquely: dimensions $d,m$, vector $b$, matrices $U,c$, and gate-index functions $o,p$. Hence $F_1.\mathrm{enc}=F_2.\mathrm{enc}$ implies $F_1=F_2$. This is the normal-form analogue of circuit-code injectivity and is used to identify the instance unpacked from an LCP answer with the normal form constructed by the reduction.
-- source:
--   Kontogiannis, Panageas, Pollatos, Yan, Finding a Positive Index Nash Equilibrium is PPADS-Complete, arXiv:2609.23879, pp. 35–36, equations (31)–(36); `NormalForm.enc` is the mission's self-delimiting encoding convention

import Mathlib
import Definitions.Def_PosIndexNash_PPADS_NormalForm_enc

theorem PosIndexNash.PPADS.normalForm_enc_injective : Function.Injective NormalForm.enc := by sorry
