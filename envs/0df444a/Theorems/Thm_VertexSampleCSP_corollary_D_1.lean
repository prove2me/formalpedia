-- Prove2me | Theorems.Thm_VertexSampleCSP_corollary_D_1
-- name    : VertexSampleCSP.corollary_D_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:56:14.593925+00:00
-- url     : https://prove2.me/theorems/96df58c9-4991-48fe-bfa8-0b7a0fa04990
-- title:
--   Corollary D.1, p.18 — expectation: $\mathbb E|(n/k)^r\mathrm{OPT}(\mathcal I[S])-\mathrm{OPT}(\mathcal I)|\le C_{r,q}n^{r/2}\sqrt{m/k}\le C'_{r,q}n^r/\sqrt k$
-- statement:
--   Let $\mathcal I$ be an instance of arity $r$ over $[q]$ on $n$ variables whose payoffs all lie in $[-1,1]$, with $m$ nonzero tables, and let $S$ be a uniformly random $k$-subset, $1\le k\le n$. With the constants $C_{r,q}$ and $C'_{r,q}$ of §D.1,
--
--   $$\mathbb E\Big|\Big(\frac nk\Big)^r\mathrm{OPT}(\mathcal I[S])-\mathrm{OPT}(\mathcal I)\Big|\le C_{r,q}\,n^{r/2}\sqrt{\frac mk}\le C'_{r,q}\,\frac{n^r}{\sqrt k}.$$
--
--   This is the expectation half of the goal theorem with explicit constants.
--
--   **Formalization Note** $n^{r/2}$ is a real power.
--
--   Differences from the source:
--
--   - encoding: arity r ≥ 2 of the section → hypothesis 2 ≤ r; reason: the standing assumption of Appendix A
--   - encoding: alphabet [q] = {1, …, q} → q ≥ 1 is a hypothesis and the alphabet is Fin q; reason: q = 0 leaves the optimum and the polytopes undefined, so this excludes only undefined cases
--   - encoding: I[S] is the instance on S → I.sub S on the subtype ↥S; reason: same instance, written in a type with |S| variables
--   - encoding: n variables → finite type V with n = |V|; reason: same instances up to the names of the variables
--   - encoding: a uniformly random k-set S → 1 ≤ k ≤ |V| and the finite average unifAvg; reason: the range of Theorem C.4(a), from which the corollary follows
-- source:
--   Chang, Optimal Vertex Sampling for Constraint Satisfaction Problems, STOC 2027 submission (manuscript sha256 1e0edd23…), Corollary D.1, p.18 (PDF p.20); the constants C_{r,q}, C′_{r,q}, p.18

import Mathlib
import Definitions.Def_VertexSampleCSP_Instance
import Definitions.Def_VertexSampleCSP_OPT
import Definitions.Def_VertexSampleCSP_Instance_sub
import Definitions.Def_VertexSampleCSP_numConstraints
import Definitions.Def_VertexSampleCSP_PayoffsIn01
import Definitions.Def_VertexSampleCSP_unifAvg
import Definitions.Def_VertexSampleCSP_Cr

namespace VertexSampleCSP

/-- **Corollary D.1 (Theorem 1.1, expectation).** Chang, *Optimal Vertex Sampling for Constraint
Satisfaction Problems*, STOC 2027 submission (manuscript sha256 1e0edd23…), Corollary D.1, p.18
(PDF p.20), with the constants of §D.1 ("Let C_{r,q} = C_r √(rq^r) = 8(1 + √2)(2^r − 1)q^{r/2}/√(r!)
and C′_{r,q} = C_{r,q}/√(r!)"): "If all payoffs of I lie in [−1, 1] and m tables are nonzero, then
for a uniformly random k-set S,
E|(n/k)^r OPT(I[S]) − OPT(I)| ≤ C_{r,q} n^{r/2} √(m/k) ≤ C′_{r,q} n^r/√k."

**Formalization Note.** The `n` variables are a finite type `V` with `n = |V|`; `1 ≤ k ≤ n` is the
range of Theorem C.4(a), from which the corollary follows. `I[S]` is the instance on the subtype
`↥S`; `[q]` is `Fin q` with `q ≥ 1`; `n^{r/2}` is a real power. -/
theorem corollary_D_1 {V : Type*} [Fintype V] [DecidableEq V] {r q : ℕ} (hr : 2 ≤ r) (hq : 0 < q)
    (I : Instance V r q) (hI : PayoffsAbsLe1 I) (k : ℕ) (hk : 1 ≤ k)
    (hkn : k ≤ Fintype.card V) :
    unifAvg k (fun S => |((Fintype.card V : ℝ) / k) ^ r * OPT (I.sub S) - OPT I|) ≤
        Crq r q * (Fintype.card V : ℝ) ^ ((r : ℝ) / 2) *
          Real.sqrt ((numConstraints I : ℝ) / k) ∧
    Crq r q * (Fintype.card V : ℝ) ^ ((r : ℝ) / 2) * Real.sqrt ((numConstraints I : ℝ) / k) ≤
        Crq' r q * (Fintype.card V : ℝ) ^ r / Real.sqrt k := by sorry

end VertexSampleCSP
