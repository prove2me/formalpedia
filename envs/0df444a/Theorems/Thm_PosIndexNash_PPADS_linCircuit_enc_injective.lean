-- Prove2me | Theorems.Thm_PosIndexNash_PPADS_linCircuit_enc_injective
-- name    : PosIndexNash.PPADS.linCircuit_enc_injective
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:01:10.008363+00:00
-- url     : https://prove2.me/theorems/52d09cfb-175f-465b-be40-d93d3db8cb4b
-- title:
--   The binary encoding of a rational Linear-FIXP circuit is injective
-- statement:
--   The binary code of a rational max-affine circuit determines the circuit uniquely: if $C_1.\mathrm{enc}=C_2.\mathrm{enc}$, then $C_1=C_2$. The code records $d_{\mathrm{in}}$, the ordered list of gate codes, and the output wires, with all rational coefficients and indices written by the standard self-delimiting binary codes. This injectivity is needed when an answer to an encoded intermediate instance is transferred back to the circuit selected by the reduction.
-- source:
--   Kontogiannis, Panageas, Pollatos, Yan, Finding a Positive Index Nash Equilibrium is PPADS-Complete, arXiv:2609.23879, p. 13, rational max-affine circuits; the encoding is the mission's `LinCircuit.enc` formalization convention

import Mathlib
import Definitions.Def_PosIndexNash_PPADS_LinCircuit

theorem PosIndexNash.PPADS.linCircuit_enc_injective : Function.Injective LinCircuit.enc := by sorry
