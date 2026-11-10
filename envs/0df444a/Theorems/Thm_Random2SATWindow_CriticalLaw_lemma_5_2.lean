-- Prove2me | Theorems.Thm_Random2SATWindow_CriticalLaw_lemma_5_2
-- name    : Random2SATWindow.CriticalLaw.lemma_5_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:42:14.033687+00:00
-- url     : https://prove2.me/theorems/07ac5071-0cf3-42d2-a4c1-d74f8cc0a9d5
-- title:
--   Lemma 5.2 — weighted implication source identity (49)
-- statement:
--   Let $\varphi$ be a function on finite simple strongly connected digraphs, with values in a commutative $\mathbb Q$-algebra, invariant under isomorphism and under reversal of all arcs. Put $S_\varphi(z,w)=\sum_{k\ge1}\frac{z^k}{k!}\sum_C\varphi(C)w^{e(C)}$, $C$ over the strongly connected digraphs on $[k]$. For a satisfiable formula $F$ put $\varphi(F)=\prod_{\{C,\bar C\}\in O(F)}\varphi(C)$, $\varphi(C)$ evaluated on the subdigraph of $D(F)$ induced by $C$, and
--   $$\ddot{\mathrm{SAT}}_\varphi(z,w)=\sum_{n\ge0}\frac{z^n}{2^nn!(1+w)^{n(n-1)}}\sum_{F\in\mathrm{SAT}_n}\varphi(F)w^{|F|}.$$
--   Then, as formal power series in $z$,
--   $$\big(e^{-S_\varphi(z,w)}\odot D_0(z,w)\big)\,\ddot{\mathrm{SAT}}_\varphi(z,w)=e^{-S_\varphi(2z,w)/2}\odot I_0(z,w).\qquad(49)$$
--   In Lean the coefficient algebra $K$ is any commutative $\mathbb Q$-algebra that contains $w$ with $1+w$ a unit, and $\varphi$ takes values in $K$.
--
--   Differences from the source:
--   - generalization: φ with values in a commutative ℚ-algebra A; the nature of w (formal variable) left implicit → any commutative ℚ-algebra K, any w ∈ K with 1 + w a unit, φ valued in K; reason: each z-coefficient of (49) is a polynomial identity in w and (1+w)^{-1} with coefficients ℚ-combinations of φ-values (the inclusion–exclusion proof uses only Σ_{S} w^{|S|} = (1+w)^{#} and the normalizations); it specializes to the formal reading K = A⟦w⟧, w = X (1 + X is a unit, φ composed with A → A⟦w⟧) and to real w > 0
--   - encoding: φ a function on finite simple strongly connected digraphs, invariant under isomorphism and arc reversal → φ : (k : ℕ) → Finset (Fin k × Fin k) → K with IsDigraphWeight φ (invariance under relabelling by Equiv.Perm (Fin k) and under prodComm, required on IsSimpleSC digraphs); reason: a finite digraph up to isomorphism is an arc set on [k] up to relabelling; values off simple strongly connected digraphs never enter S_φ or φ(F)
--   - encoding: φ(C) evaluated on the subdigraph of D(F) induced by C; one factor per mirror orbit {C, C̄} → φ |C| (inducedArcs F C) with C relabelled by Finset.equivFin, orbit member chosen by orbitRep; reason: for an invariant φ the value does not depend on these choices (the paper's own well-definedness remark)
--   - encoding: e^{f}, f(2z), ⊙, (1+w)^{-m} → expOf f = PowerSeries.subst f (exp K), doubleArg = rescale 2, expHadamard ([z^k] = k!·[z^k]f·[z^k]g), Ring.inverse (1+w) ^ m; reason: definitions; Ring.inverse is the inverse because 1 + w is a unit
--   - encoding: 2-SAT formulas: sets of distinct legal clauses on two distinct variables; F(n, p) independent clauses, F(n, m) uniform m-subsets of the N_n = 2n(n−1) legal clauses → LegalClause n = unordered pairs (Sym2) of literals Fin n × Bool whose variables differ, Formula n = Finset (LegalClause n); probBinom n p E = Σ_{F ∈ E} p^{|F|}(1−p)^{N_n−|F|}, satProbUniform n m = #{F : |F| = m, F ∈ SAT}/C(N_n, m); reason: the paper's model verbatim; N_n = Fintype.card (LegalClause n) = 2n(n−1)
-- source:
--   Ravelomanana, Inside the Critical Window of Random 2-SAT, STOC 2027 submission (manuscript sha256 eef2fa67…), Lemma 5.2, printed p. 23 (PDF 25); proof printed p. 24 (PDF 26)

import Mathlib
import Definitions.Def_Random2SATWindow_CriticalLaw_Formulas
import Definitions.Def_Random2SATWindow_CriticalLaw_Airy
import Definitions.Def_Random2SATWindow_CriticalLaw_Hadamard
import Definitions.Def_Random2SATWindow_CriticalLaw_Strata
import Definitions.Def_Random2SATWindow_CriticalLaw_Saddle
import Definitions.Def_Random2SATWindow_CriticalLaw_PureLiteral

set_option autoImplicit false

open Filter Topology MeasureTheory

namespace Random2SATWindow.CriticalLaw

/-- **Lemma 5.2** (weighted implication source identity, printed p. 23–24 / PDF 25–26). Let `φ`
be a weight on finite simple strongly connected digraphs, with values in a commutative
`ℚ`-algebra, invariant under isomorphism and under reversal of all arcs. Then, as formal power
series in `z`,
`(e^{-S_φ(z,w)} ⊙ D_0(z,w)) · S̈AT_φ(z,w) = e^{-S_φ(2z,w)/2} ⊙ I_0(z,w)` (49).
The weight `w` is any element of the coefficient algebra with `1 + w` a unit (a formal `w`, or a
real `w > 0`). -/
theorem lemma_5_2 {K : Type*} [CommRing K] [Algebra ℚ K]
    (φ : (k : ℕ) → Finset (Fin k × Fin k) → K) (hφ : IsDigraphWeight φ)
    (w : K) (hw : IsUnit (1 + w)) :
    expHadamard (expOf (-SPhi φ w)) (D0 w) * SATPhi φ w =
      expHadamard (expOf (-((1 / 2 : ℚ) • doubleArg (SPhi φ w)))) (I0 w) := by sorry

end Random2SATWindow.CriticalLaw
