-- Prove2me | Theorems.Thm_VertexSampleCSP_lemma_C_3
-- name    : VertexSampleCSP.lemma_C_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:55:58.592261+00:00
-- url     : https://prove2.me/theorems/7dc9b715-8968-412d-92b8-fe45dddc5051
-- title:
--   Lemma C.3, p.17 — the scale under sampling: $\mathbb E\,\Gamma(\mathcal I[S])\le(N^\prime/N)^{(r+1)/2}\Gamma(\mathcal I)$
-- statement:
--   Let $\mathcal I$ be an instance on $N$ variables.
--
--   1. If $S$ is a uniformly random subset of size $N'\le N$ of the variables, then
--
--   $$\mathbb E\,\Gamma(\mathcal I[S])\le(N'/N)^{(r+1)/2}\,\Gamma(\mathcal I).$$
--
--   2. If $S$ contains every variable independently with probability $p$, then
--
--   $$\mathbb E\,\Gamma(\mathcal I[S])\le p^{(r+1)/2}\,\Gamma(\mathcal I).$$
--
--   The scale of a sample decays fast enough that the per-step errors along the chain of Theorem C.4 sum to a geometric series.
--
--   **Formalization Note** The exponents are real powers. At $N=0$ the ratio is Lean's $0/0=0$, but then $N'=0$ and both sides are $0$.
--
--   Differences from the source:
--
--   - encoding: arity r ≥ 2 of the section → hypothesis 2 ≤ r; reason: the standing assumption of Appendix A
--   - encoding: alphabet [q] = {1, …, q} → q ≥ 1 is a hypothesis and the alphabet is Fin q; reason: q = 0 leaves the optimum and the polytopes undefined, so this excludes only undefined cases
--   - encoding: I[S] is the instance on S → I.sub S on the subtype ↥S; reason: same instance, written in a type with |S| variables
--   - encoding: with probability p → 0 ≤ p ≤ 1; reason: the range in which p is a probability
--   - encoding: E over the random subset → the finite averages unifAvg and bernAvg; reason: same expectations
-- source:
--   Chang, Optimal Vertex Sampling for Constraint Satisfaction Problems, STOC 2027 submission (manuscript sha256 1e0edd23…), Lemma C.3, p.17 (PDF p.19)

import Mathlib
import Definitions.Def_VertexSampleCSP_Instance
import Definitions.Def_VertexSampleCSP_Instance_sub
import Definitions.Def_VertexSampleCSP_Instance_Gamma
import Definitions.Def_VertexSampleCSP_bernAvg
import Definitions.Def_VertexSampleCSP_unifAvg

namespace VertexSampleCSP

/-- **Lemma C.3 (The scale under sampling).** Chang, *Optimal Vertex Sampling for Constraint
Satisfaction Problems*, STOC 2027 submission (manuscript sha256 1e0edd23…), Lemma C.3, p.17 (PDF
p.19): "If S is a uniformly random subset of size N′ ≤ N of the variables of I, then
E Γ(I[S]) ≤ (N′/N)^{(r+1)/2} Γ(I). If S contains every variable independently with probability p,
then E Γ(I[S]) ≤ p^{(r+1)/2} Γ(I)."

For an instance `I` on `N = |V|` variables:
1. for `N′ ≤ N` and a uniformly random `N′`-subset `S`: `E Γ(I[S]) ≤ (N′/N)^{(r+1)/2} Γ(I)`;
2. for `p ∈ [0, 1]` and a Bernoulli(`p`) subset `S`: `E Γ(I[S]) ≤ p^{(r+1)/2} Γ(I)`.

**Formalization Note.** `Γ(I[S])` is `Γ` of the instance on the subtype `↥S`. The exponents are real
powers. At `N = 0` the ratio `N′/N` is Lean's `0/0 = 0`, but then `N′ = 0` and both sides are `0`, so
the statement needs no `N ≥ 1`. -/
theorem lemma_C_3 {V : Type*} [Fintype V] [DecidableEq V] {r q : ℕ} (hr : 2 ≤ r) (hq : 0 < q)
    (I : Instance V r q) :
    (∀ N' : ℕ, N' ≤ Fintype.card V →
      unifAvg N' (fun S => (I.sub S).Gamma) ≤
        ((N' : ℝ) / Fintype.card V) ^ (((r : ℝ) + 1) / 2) * I.Gamma) ∧
    (∀ p : ℝ, 0 ≤ p → p ≤ 1 →
      bernAvg p (fun S => (I.sub S).Gamma) ≤ p ^ (((r : ℝ) + 1) / 2) * I.Gamma) := by sorry

end VertexSampleCSP
