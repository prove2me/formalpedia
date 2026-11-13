-- Prove2me | Theorems.Thm_SubspaceEvasion312_Explicit_local_to_global
-- name    : SubspaceEvasion312.Explicit.local_to_global
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-11T04:00:29.085793+00:00
-- url     : https://prove2.me/theorems/2f98e157-2adb-4725-8845-678c7f0020f0
-- title:
--   Theorem 8 — local-to-global graph composition
-- statement:
--   There is an absolute $K>0$. Let $F$ be any field, $C\le(F^s)^m$, $k=\dim_F C$, and $E:F^k\to(F^s)^m$ a linear encoder with image $C$. Suppose $G^f$ is $(r,c)$ evasive and $C$ is $(r,0,c,L)$ subspace list-recoverable. The actual function $g(x)_i=f(E(x)_i)$ satisfies
--
--   $$G^g\text{ is }(r,L)\text{ subspace evasive},\qquad F^k\simeq G^g.$$
--
--   The encoder is injective as a consequence of its dimension and image conditions. The graph bijection is $x\mapsto(x,g(x))$, also over infinite fields; low-dimensional intersections are explicitly finite. When $F=F_q$ is finite, $|G^g|=q^k$.
--
--   For finite fields, given actual evaluator programs for $f$ and $E$ taking times $T_f,T_C$, there are programs evaluating $g$, constructing its indexed graph point, and deciding membership on every input, all in time $K(T_C+mT_f)$. The conclusion also supplies a polynomial bound on their natural registers in terms of the supplied bounds, times and dimensions. This retains all three effectiveness clauses of the source.
--
--   Differences from the source:
--   - reading: a field F in the hypotheses and F_q in the graph and cardinality → the algebraic graph theorem over arbitrary F, and numerical q^k cardinality and indexed costs over finite fields; reason: resolves the source field-notation switch without narrowing its algebraic conclusion
--   - encoding: an encoder with dim_F C=k and graph cardinality → a linear map with range C and k=dim_F C, explicit injectivity conclusion, finite low-dimensional intersections, and the canonical graph bijection; reason: does not assume injectivity as extra data and does not use ncard=0 on infinite sets to make evasion vacuous
--   - encoding: the three O(T_C+mT_f) effectiveness clauses → three finite register programs with one universal multiplier, charged setup, and an explicit bound on natural words; reason: their outputs are the actual composition, the indexed graph point and the true indicator; input indices use standard base-q field digits
-- source:
--   Brakensiek, Chen, Cheraghchi, Goyal, Guruswami, Putterman, Zhang, STOC 2027 submission #312 (October 2026), Theorem 8, printed p. 7 (PDF p. 8); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/312.pdf; PDF SHA256 a6946cb436bf453cfc53c1547fdd79e55134761b2192ee39f145dfc45490f6bc; proof continued printed p. 8 (PDF p. 9)

import Definitions.Def_SubspaceEvasion312_Explicit_effective

namespace SubspaceEvasion312.Explicit
open scoped ENNReal
/-- Theorem 8, printed pp.7-8 (PDF pp.8-9). The algebraic claim is over
an arbitrary field, while cardinality and indexed computation specialize to finite fields. -/
theorem local_to_global :
    ∃ K : ℕ, 0 < K ∧
    ∀ (F : Type) [Field F] (s b m k r c L : ℕ)
      (C : Code F s m) (E : Vec F k →ₗ[F] Blocks F s m)
      (f : Vec F s → Vec F b),
      IsEncoder C E → Evasive (F := F) (graph f) r c → ListRecoverable C r 0 c L →
      Function.Injective E ∧ Evasive (F := F) (graph (compose E f)) r L ∧
      (∃ e : Vec F k ≃ graph (compose E f), ∀ x, (e x).val = (x, compose E f x)) ∧
      (∀ [Fintype F], (graph (compose E f)).ncard = (Fintype.card F)^k ∧
        ∀ (Pf PC : Program F) (Tf TC Bf BC : ℕ),
          Evaluates Pf f Tf Bf → EvaluatesBlocks PC (fun x => E x) TC BC →
          ∃ (Pg PI PM : Program F) (B : ℕ),
            B ≤ (Bf + BC + TC + m*Tf + k + b*m + s*m + 2)^K ∧
            GraphAlgorithms (compose E f) Pg PI PM (K*(TC + m*Tf)) B) := by sorry
end SubspaceEvasion312.Explicit
