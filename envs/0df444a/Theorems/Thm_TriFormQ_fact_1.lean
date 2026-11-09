-- Prove2me | Theorems.Thm_TriFormQ_fact_1
-- name    : TriFormQ.fact_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:56:26.5432+00:00
-- url     : https://prove2.me/theorems/f3ccbc3b-f286-47fb-a91e-02d7aa4c11c0
-- title:
--   Fact 1: good fibers have $\mathbb E\,q^{\mathrm{rk} f[u]}\le 8q^{\mathrm{AR}(f)}$ and codimension $\le\mathrm{AR}(f)+\log_q 8$, and $p_Z(G)\ge 3/4$
-- statement:
--   Let $f$ be a trilinear form on $\mathbb F_q^n$ with good set $G$. Then:
--
--   1. for every $v\in G$, $M(v)=\mathbb E_{u\in Z_v}q^{\mathrm{rk} f[u]}\le 8\,q^{\mathrm{AR}(f)}$;
--   2. for every $v\in G$, the fiber $Z_v$ has codimension $\mathrm{codim}(Z_v)\le \mathrm{AR}(f)+\log_q 8$;
--   3. a base point drawn from $p_Z$ is good with probability at least $3/4$:
--   $$\Pr_{v\sim p_Z}[v\in G]=\sum_{v\in G}p_Z(v)\ \ge\ \frac34 .$$
--
--   These are the properties of good fibers the later stages use: a good fiber is a large subspace on which the slices $f[u]$ have small average size, and good base points carry most of the mass of $p_Z$.
--
--   Differences from the source:
--   - encoding: $\mathrm{codim}(Z_v)$ and $\Pr_{v\sim p_Z}[v\in G]$ → $n-\dim$ of the fiber subspace, and $\sum_{v\in G}p_Z(v)$; reason: definitions of codimension and of the probability under $p_Z$
-- source:
--   Grigorescu–Juba–Wimmer–Xie, Optimal Quantum Query Bounds for Identifying Classes of 3-Tensors, STOC 2027 submission (manuscript sha256 c56b0365…), Fact 1 and Eq. (4), p.22 (PDF p.25)

import Definitions.Def_TriFormQ_goodSet
import Definitions.Def_TriFormQ_fiberSub
import Definitions.Def_TriFormQ_pZ

namespace TriFormQ

/-- Grigorescu–Juba–Wimmer–Xie, *Optimal Quantum Query Bounds for Identifying Classes of
3-Tensors*, STOC 2027 submission (manuscript sha256 c56b0365…), Fact 1 and Eq. (4), p.22
(PDF p.25): "For any v ∈ G, the fiber Z_v of U over v satisfies the following properties:
• E_{u∈Z_v}[q^{rk f[u]}] ≤ 8q^{AR(f)} • codim(Z_v) ≤ AR(f) + log_q 8. Moreover, if v is sampled
according to p_Z from V, then the probability that v falls in G is at least 3/4, i.e.,
Pr_{v∼p_Z}[v ∈ G] ≥ 3/4."

**Formalization Note.** `codim(Z_v)` is `n − finrank` of the fiber subspace `fiberSub θ v`, and
`Pr_{v∼p_Z}[v ∈ G]` is `Σ_{v∈G} p_Z(v)`. All three clauses are stated. -/
theorem fact_1 {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ} (θ : TriForm F n) :
    (∀ v ∈ goodSet θ, Mv θ v ≤ 8 * (Fintype.card F : ℝ) ^ AR θ ∧
      (n : ℝ) - Module.finrank F (fiberSub θ v) ≤ AR θ + Real.logb (Fintype.card F) 8) ∧
    (3 / 4 : ℝ) ≤ ∑ v ∈ goodSet θ, pZ θ v := by sorry

end TriFormQ
