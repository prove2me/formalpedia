-- Prove2me | Theorems.Thm_VertexSampleCSP_theorem_C_4
-- name    : VertexSampleCSP.theorem_C_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:55:55.087543+00:00
-- url     : https://prove2.me/theorems/d7e9179b-4784-4542-852a-15e4146a537a
-- title:
--   Theorem C.4, p.17 — sampling theorem: expected error at most $C_rn^{(r-1)/2}\Gamma(\mathcal I)/\sqrt k$ (corrected: strict bound in (b) for $\Gamma(\mathcal I)>0$)
-- statement:
--   Let $\mathcal I$ be an instance of arity $r$ over $[q]$ on $n$ variables with real payoffs, and let $C_r=8(1+\sqrt2)(2^r-1)/\sqrt{r\cdot r!}$.
--
--   (a) If $S$ is a uniformly random $k$-subset, $1\le k\le n$, then
--
--   $$\mathbb E\Big|\Big(\frac nk\Big)^r\mathrm{OPT}(\mathcal I[S])-\mathrm{OPT}(\mathcal I)\Big|\le C_r\,n^{(r-1)/2}\,\frac{\Gamma(\mathcal I)}{\sqrt k}.$$
--
--   (b) If $r=2$ and $S_p$ contains every variable independently with probability $p\in(0,1]$, then
--
--   $$\mathbb E\big|p^{-2}\mathrm{OPT}(\mathcal I[S_p])-\mathrm{OPT}(\mathcal I)\big|\le(12+3\sqrt2)\frac{\Gamma(\mathcal I)}{\sqrt p},$$
--
--   and $(12+3\sqrt2)\Gamma(\mathcal I)/\sqrt p<17\,\Gamma(\mathcal I)/\sqrt p$ when $\Gamma(\mathcal I)>0$.
--
--   Part (a) is the refined form of the goal theorem, in the scale $\Gamma$ in which instances with uneven degrees need fewer samples. Part (b) is the vertex-percolation form for pairwise problems.
--
--   Differences from the source:
--
--   - correction: (12 + 3√2)Γ(I)/√p < 17Γ(I)/√p with no condition → the strict inequality under 0 < Γ(I); reason: it is false at Γ(I) = 0, for instance for the instance whose tables all vanish: both sides are 0
--   - encoding: arity r ≥ 2 of the section → hypothesis 2 ≤ r; reason: the standing assumption of Appendix A
--   - encoding: alphabet [q] = {1, …, q} → q ≥ 1 is a hypothesis and the alphabet is Fin q; reason: q = 0 leaves the optimum and the polytopes undefined, so this excludes only undefined cases
--   - encoding: I[S] is the instance on S → I.sub S on the subtype ↥S; reason: same instance, written in a type with |S| variables
--   - encoding: n variables → finite type V with n = |V|; reason: same instances up to the names of the variables
--   - encoding: E over the random subset → the finite averages unifAvg and bernAvg; reason: same expectations
-- source:
--   Chang, Optimal Vertex Sampling for Constraint Satisfaction Problems, STOC 2027 submission (manuscript sha256 1e0edd23…), Theorem C.4, p.17 (PDF p.19); the constant C_r, p.17

import Mathlib
import Definitions.Def_VertexSampleCSP_Instance
import Definitions.Def_VertexSampleCSP_OPT
import Definitions.Def_VertexSampleCSP_Instance_sub
import Definitions.Def_VertexSampleCSP_Instance_Gamma
import Definitions.Def_VertexSampleCSP_bernAvg
import Definitions.Def_VertexSampleCSP_unifAvg
import Definitions.Def_VertexSampleCSP_Cr

namespace VertexSampleCSP

/-- **Theorem C.4 (Sampling theorem).** Chang, *Optimal Vertex Sampling for Constraint Satisfaction
Problems*, STOC 2027 submission (manuscript sha256 1e0edd23…), Theorem C.4, p.17 (PDF p.19), with
the constant of p.17 ("Let Cr = 8(1 + √2)(2^r − 1)/√(r · r!)"): "Let I be an instance of arity r
over [q] on n variables with real payoffs.
(a) If S is a uniformly random k-subset, 1 ≤ k ≤ n, then
E |(n/k)^r OPT(I[S]) − OPT(I)| ≤ Cr n^{(r−1)/2} Γ(I)/√k.
(b) If r = 2 and Sp contains every variable independently with probability p ∈ (0, 1], then
E |p^{−2} OPT(I[Sp]) − OPT(I)| ≤ (12 + 3√2) Γ(I)/√p < 17 Γ(I)/√p."

**Formalization Note.** The `n` variables are a finite type `V` with `n = |V|`. `I[S]` is the
instance on the subtype `↥S`. Payoffs are arbitrary reals; `[q]` is `Fin q` with `q ≥ 1`. The trailing
strict inequality of (b) is stated for `Γ(I) > 0`: at `Γ(I) = 0` both of its sides are `0`. -/
theorem theorem_C_4 {V : Type*} [Fintype V] [DecidableEq V] {r q : ℕ} (hr : 2 ≤ r) (hq : 0 < q)
    (I : Instance V r q) :
    (∀ k : ℕ, 1 ≤ k → k ≤ Fintype.card V →
      unifAvg k (fun S => |((Fintype.card V : ℝ) / k) ^ r * OPT (I.sub S) - OPT I|) ≤
        Cr r * (Fintype.card V : ℝ) ^ (((r : ℝ) - 1) / 2) * I.Gamma / Real.sqrt k) ∧
    (r = 2 → ∀ p : ℝ, 0 < p → p ≤ 1 →
      bernAvg p (fun S => |(p ^ 2)⁻¹ * OPT (I.sub S) - OPT I|) ≤
          (12 + 3 * Real.sqrt 2) * I.Gamma / Real.sqrt p ∧
        (0 < I.Gamma →
          (12 + 3 * Real.sqrt 2) * I.Gamma / Real.sqrt p < 17 * I.Gamma / Real.sqrt p)) := by sorry

end VertexSampleCSP
