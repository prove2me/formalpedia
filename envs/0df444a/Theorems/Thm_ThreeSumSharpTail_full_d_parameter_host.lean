-- Prove2me | Theorems.Thm_ThreeSumSharpTail_full_d_parameter_host
-- name    : ThreeSumSharpTail.full_d_parameter_host
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-13T19:11:16.98443+00:00
-- url     : https://prove2.me/theorems/ae24ddcb-1040-45db-98cb-67eb67701653
-- title:
--   Full dimension Exact Triangle host for arbitrary rational power parameters
-- statement:
--   For natural a,b,c,e with b,e>=1, a<=b and 2c<=e, the actual light-model full dimension host satisfies Theorem 17 for D(n)=floor(n^(a/b)) and g(n)=ceil(D(n)^(c/e)). The theorem also supplies these exact floor and ceiling identities. The host is assembled from finite rational-parameter routines, actual Exact Triangle program correctness, and polynomial word, cell and depth needs. No middle-dimension or fixed-parameter result is assumed.
-- source:
--   Generic assembly and parameter-procedure proofs from the accepted full-D Exact Triangle and claim_aeUniform_mid source snapshots; uses the existing Proved et17_spec and obeysBound17_hostTime interfaces, while excluding the fixed numerical conclusions.

import Definitions.Def_APSP299791_Defs5

theorem ThreeSumSharpTail.full_d_parameter_host (a b c e : ℕ) (hb : 1 ≤ b) (he : 1 ≤ e)
    (hab : a ≤ b) (hce : 2 * c ≤ e) :
    ThreeSumApsp.Claim.Theorem_17 Light.lightModel ThreeSumApsp.strassen
      (fun n => ThreeSumApsp.paramDr a b n)
      (fun n => ThreeSumApsp.paramGr c e (ThreeSumApsp.paramDr a b n)) ∧
      (∀ n, ThreeSumApsp.paramDr a b n = ⌊(n : ℝ) ^ ((a : ℝ) / b)⌋₊) ∧
      (∀ D, 1 ≤ D → ThreeSumApsp.paramGr c e D = ⌈(D : ℝ) ^ ((c : ℝ) / e)⌉₊) := by sorry
