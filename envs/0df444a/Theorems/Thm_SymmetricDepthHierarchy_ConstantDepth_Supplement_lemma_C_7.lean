-- Prove2me | Theorems.Thm_SymmetricDepthHierarchy_ConstantDepth_Supplement_lemma_C_7
-- name    : SymmetricDepthHierarchy.ConstantDepth.Supplement.lemma_C_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T11:12:45.942688+00:00
-- url     : https://prove2.me/theorems/a2e3b74a-6c0e-4afc-a403-4df1733a86ca
-- title:
--   Lemma C.7 — Counting equivalence forces equality on weighted matrices
-- statement:
--   Over a characteristic-zero field, use the same equal-side-size, one-label-per-pair hosts and padding bound as Lemma C.6. Let k,q>=1 and suppose the hosts agree on all k-variable counting sentences of rank at most q. Every weight vector and every polynomial in the indicated linear span give equal evaluations; isolated pattern vertices are retained.
--
--   $$
--   G\equiv_{C_k^q}H\Rightarrow p(M_G^\omega)=p(M_H^\omega)\quad\text{for every }\omega\text{ and }p\in\operatorname{span}_K\{\operatorname{hom}_{F,N}:F\in\mathcal T_q^k\}.
--   $$
--
--   This result supports Theorem C.10; it retains all clauses of the source result and supplies its stated interface to the remaining companion results.
--
--   Differences from the source:
--   - encoding: finite circuits, patterns and positive matrix indices with polynomial and logarithmic resource bounds → the published circuit and pattern interfaces, finite ordinal witnesses, positive host indices and explicit eventual quantifiers; reason: finite relabelling preserves semantics and full automorphism orbits; index zero is outside X_n and no degree or total-size cap is added
--   - encoding: zero-padded weighted matrices with unspecified vertex indexing → arbitrary explicit injective row and column indexings, for each host separately; reason: the stated cardinality bounds guarantee such injections and homomorphism polynomials are unchanged by reindexing
-- source:
--   Anuj Dawar, Prateek Dwivedi, Benedikt Pago, Tim Seppelt, STOC 2027 submission #1521 (October 2026), p. 45 (PDF p. 48), Lemma C.7; source.pdf sha256 e2d54636eb14a5004f0538279b05a710bdf6487b706704a71bea70f01e7b4c42

import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Supplement_Logic

set_option autoImplicit false
open scoped Classical
noncomputable section

namespace SymmetricDepthHierarchy.ConstantDepth.Supplement

theorem lemma_C_7 (K : Type) [Field K] [CharZero K]
    {SLabel : Type} [Fintype SLabel] (G H : LabelledHost SLabel)
    (hG : G.oneLabel) (hH : H.oneLabel)
    (hA : Fintype.card G.A = Fintype.card H.A) (hB : Fintype.card G.B = Fintype.card H.B)
    (N : ℕ) (hNA : Fintype.card G.A ≤ N) (hNB : Fintype.card G.B ≤ N)
    (gA : G.A ↪ Fin N) (gB : G.B ↪ Fin N) (hAi : H.A ↪ Fin N) (hBi : H.B ↪ Fin N)
    (k q : ℕ) (hk : 1 ≤ k) (hq : 1 ≤ q)
    (hequiv : countingEquiv G.structureOf H.structureOf k q) :
    ∀ ω : SLabel → K, ∀ p ∈ homSpan K N {F | inT F.G k q},
      MvPolynomial.eval (fun ij => G.weightedMatrix gA gB ω ij.1 ij.2) p =
      MvPolynomial.eval (fun ij => H.weightedMatrix hAi hBi ω ij.1 ij.2) p := by sorry

end SymmetricDepthHierarchy.ConstantDepth.Supplement
