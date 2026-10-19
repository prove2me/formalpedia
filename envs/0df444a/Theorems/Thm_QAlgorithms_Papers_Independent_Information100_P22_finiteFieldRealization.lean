-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P22_finiteFieldRealization
-- name    : QAlgorithms.Papers.Independent.Information100.P22.finiteFieldRealization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:07:17.234506+00:00
-- url     : https://prove2.me/theorems/56548b10-880d-4972-bae4-2d200fab4567
-- title:
--   §S1.5, unnumbered: explicit AME encoder and decoder
-- statement:
--   Let $k\ge2$, identify the computational basis with a finite field $F$ of cardinality $d=2^k$, and choose $\lambda\in F\setminus\{0,1\}$. The encoder is $|a,s\rangle\mapsto|a+s,a+\lambda s\rangle$, and the Choi state is
--   $$|\Omega_\lambda\rangle=d^{-1}\sum_{a,s\in F}|a,a+s,a+\lambda s,s\rangle.$$
--   Both this encoder and the decoder $|u,n\rangle\mapsto|u-\lambda n,u+(1-\lambda)n\rangle$ are unitary. The Choi state is AME$(4,d)$, the signal channel is completely depolarizing, and tracing the decoder's second output gives a CPTP channel that exactly reverses the authorized channel on every input operator. This constructs the single-output task while preserving external reference correlations.
-- source:
--   Beyond Maximal Entanglement : Exact Resources for Multiparty Encrypted Quantum Cloning, arXiv:2609.28241v1, PDF p. 25, §S1.5, unnumbered: explicit AME encoder and decoder

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22

namespace QAlgorithms.Papers.Independent.Information100.P22

open scoped ComplexConjugate ComplexOrder Matrix

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

local instance {I : Type*} [Fintype I] [DecidableEq I] (G : CutGraph I) :
    Fintype (cutKernel G) := Fintype.ofFinite _

/-- §S1.5, PDF p.25: explicit encoder, AME vector, concealment and decoder channel equality. -/
theorem finiteFieldRealization (k : ℕ) (hk : 2 ≤ k) (F : Type*) [Field F] [Fintype F]
    [DecidableEq F] (hcard : Fintype.card F = 2^k) (lam : F) (h0 : lam ≠ 0) (h1 : lam ≠ 1) :
    fieldEncoder lam ∈ Matrix.unitaryGroup (F × F) ℂ ∧
    fieldDecoder lam ∈ Matrix.unitaryGroup (F × F) ℂ ∧ AMEFour (fieldChoi lam) ∧
    IsChannel (fun X => traceRight (conjSuperop (fieldDecoder lam) X)) ∧
    (∀ X : Op F, traceRight (fieldAuthorized lam X) = X.trace • mixed F) ∧
    (∀ X : Op F, traceRight (conjSuperop (fieldDecoder lam) (fieldAuthorized lam X)) = X) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P22
