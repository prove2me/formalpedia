-- Prove2me | Theorems.Thm_QuantumSepPoly_Frobenius_lemma_5_4
-- name    : QuantumSepPoly.Frobenius.lemma_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:13:12.401222+00:00
-- url     : https://prove2.me/theorems/c0fb6819-9f4a-4e1c-9884-4514b1df8558
-- title:
--   Lemma 5.4 — Valid bounded predicates
-- statement:
--   Let $d\ge1$, $D$ be any complex bipartite matrix, and $0<\eta<1$. Use the constructed disk alphabet, $\gamma=d^2\|D\|_{\max}$, $\kappa,\lambda$, and $s=\gamma\kappa^4+2\lambda(\kappa^2+1)^2+1$. Every predicate of the explicit four-slot construction satisfies
--   $$0\le P_{a,b,c,e}(z_a,z_b,z_c,z_e)\le1.$$
--   All ordered quadruples, including repeated indices, are included. Thus the reduction produces bounded predicates rather than assuming their bounds.
--
--   Differences from the source:
--   - encoding: coordinates labelled 1 through d → coordinates indexed by Fin d from 0 through d-1; reason: canonical relabelling preserves all vectors, matrices, sums, and constraints
--   - generalization: the projected flat matrix and symbols supplied by an assignment → any complex matrix and four independently supplied symbols from its constructed alphabet; reason: the entrywise estimate proves the same range bound without Hermiticity and includes all source assignments with repeated indices
-- source:
--   Giulio Malavolta, STOC 2027 submission #1577 (October 2026), Lemma 5.4, p. 20 (PDF p. 20); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1577.pdf

import Definitions.Def_QuantumSepPoly_Frobenius_CSPReduction

namespace QuantumSepPoly.Frobenius

/-- Lemma 5.4, p.20. Bounds are proved for the explicit predicate, not assumed
in the definition of the reduction. All four argument slots are independently bounded. -/
theorem lemma_5_4 (d : ℕ) (hd : 0 < d) (D : Bip d) (η : ℝ) (hη : 0 < η) (hη1 : η < 1)
    (t : Fin 4 → Fin d) (z : Fin 4 → ReductionSymbol (reductionGamma D) η) :
    reductionPredicate D η t (fun i => (z i).val) ∈ Set.Icc (0 : ℝ) 1 := by sorry

end QuantumSepPoly.Frobenius
