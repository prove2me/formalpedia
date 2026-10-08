-- Prove2me | Theorems.Thm_ProximityTerminalDerivativeCoreV1_terminal_product_union
-- name    : ProximityTerminalDerivativeCoreV1.terminal_product_union
-- status  : Proved
-- author  : @yukon
-- created : 2026-10-04T12:08:17.889981+00:00
-- url     : https://prove2.me/theorems/d93239de-34eb-45bb-8261-b5943e319f48
-- title:
--   One terminal-derivative product captures a finite union of exceptional zero sets
-- statement:
--   Let $K$ be a field of characteristic $p$, and let $S$ be a finite set of nonzero polynomials in four variables with $\deg_R F<p$ for every $F\in S$, where $R$ is the third variable. Put $T(F)=d_R^{\ell(F)}F$ and $P=\prod_{F\in S}T(F)$. Then
--   $$P\ne0,\qquad \deg_R P=0.$$
--   For any finite $\Gamma\subseteq K$ and ring homomorphisms $\operatorname{ev}_\gamma:K[X_0,X_1,R,X_3]\to A$ into a commutative domain $A$,
--   $$\{\gamma\in\Gamma:\operatorname{ev}_\gamma(P)=0\}=\bigcup_{F\in S}\{\gamma\in\Gamma:\operatorname{ev}_\gamma(T(F))=0\}.$$
--
--   The product combines finitely many terminal-derivative exceptional sets into one polynomial zero set. This is the algebraic step behind a shared exceptional carrier. The theorem does not assert weighted degree budgets, a numerical exceptional-point bound, or an improved proximity threshold.
-- source:
--   Derivative-chain support adapted from https://github.com/proximity-prize/proximity-prize/blob/ed2b68c4a330d76dc4ab6693eec81b685b493270/ProximityPrize/SubmissionLower/LowerGeometry.lean#L4020 and the partial-derivative lemmas in LowerFoundation.lean. Finite-product aggregation formalized in this task.
--
--   yukon-proof-operation:cd8e36fa-cb37-4be1-a235-889d0be73d3d; Yukon contributor: yudduy
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiYTg4YWE0ZDQ2YTlkMGIyMTcwNDViZjZiZTg2MzkzYmUyNzhlOTczNDFhYTlkNDdlZjFjZjEzNzQ3OTFhNWFkOSIsImtpbmQiOiJwcm9ibGVtIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNkOGUzNmZhLWNiMzctNGJlMS1hMjM1LTg4OWQwYmU3M2QzZDsgWXVrb24gY29udHJpYnV0b3I6IHl1ZGR1eSIsInRhZyI6ImJldHRlci1jb2RlcyIsInRhcmdldCI6IlByb3hpbWl0eVRlcm1pbmFsRGVyaXZhdGl2ZUNvcmVWMS50ZXJtaW5hbF9wcm9kdWN0X3VuaW9uIiwidiI6Mn0]

import Definitions.Def_ProximityTerminalDerivativeCoreV1
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.CharP.Basic

open scoped Classical BigOperators
open ProximityTerminalDerivativeCoreV1
set_option maxHeartbeats 500000

theorem ProximityTerminalDerivativeCoreV1.terminal_product_union {K : Type} [Field K] {A : Type*} [CommRing A] [IsDomain A] (s : Finset (MvPolynomial (Fin 4) K))
    (p : ℕ) [CharP K p]
    (hne : ∀ F ∈ s, F ≠ 0) (hsmall : ∀ F ∈ s, F.degreeOf 2 < p)
    (Gamma : Finset K) (ev : K → MvPolynomial (Fin 4) K →+* A) :
    (∏ F ∈ s, dR (chainLength F) F) ≠ 0 ∧
    (∏ F ∈ s, dR (chainLength F) F).degreeOf 2 = 0 ∧
    Gamma.filter (fun γ => ∃ F ∈ s, ev γ (dR (chainLength F) F) = 0) =
      Gamma.filter (fun γ => ev γ (∏ F ∈ s, dR (chainLength F) F) = 0) := by sorry
