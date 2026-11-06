-- Prove2me | Theorems.Thm_TemporalVoter_theorem_1_3_claim
-- name    : TemporalVoter.theorem_1_3_claim
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:14:15.043189+00:00
-- url     : https://prove2.me/theorems/e2f96b29-089a-4066-9b6e-a03feb693d6c
-- title:
--   Claim in the proof of Theorem 1.3 — a metaphase ends within $\xi_\alpha$ phases with probability at least $1/3$
-- statement:
--   Let $b>0$ be a constant for which the conclusion of Theorem 3.1 holds and let $B>0$. Consider the standard voter model with any number of opinions on a temporal graph $\mathcal G$ with fixed degrees, $m$ edges and minimum degree $d_{\min}$, from any initial state, with integers $\Delta_j\ge1$ and reals $\phi_j\in[0,1]$ such that $\phi^{I_j}(\mathcal G)\ge\phi_j$ for all $j$, and such that the phases $t_r$ ($r\le r_{\max}=\lfloor Bm/d_{\min}\rfloor$) exist. Let $R_\alpha$ be the metaphase boundaries and $\mathcal O(t)$ the set of opinions present at time $t$.
--
--   Let $r,\alpha\ge0$, let $H$ be a possible value of the history $\mathcal H_{t_r}=(\xi_0,\dots,\xi_{t_r})$, and suppose that $\mathcal H_{t_r}=H$ determines $R_\alpha\le r<R_{\alpha+1}$. Let $r_\alpha$ and $O_\alpha$ be the values of $R_\alpha$ and $\mathcal O(t_{r_\alpha})$ determined by $H$, and let
--   $$\xi_\alpha:=1+\Bigl\lceil b\Bigl(\frac{6m}{d_{\min}|O_\alpha|}+\log\bigl(1+6m/|O_\alpha|\bigr)\Bigr)\Bigr\rceil.$$
--   Then
--   $$\mathbb P\bigl(R_{\alpha+1}>r+\xi_\alpha\bigm|\mathcal H_{t_r}=H\bigr)\le\frac23.$$
--
--   Applied repeatedly, it makes the number of phases in a metaphase stochastically dominated by a geometric variable, which bounds the time until one opinion remains.
--
--   Differences from the source:
--   - encoding: the voter process (ξ_t : t ≥ 0) of Definition 1.2 on some probability space → the path measure voterLaw on ℕ → (V → Fin k), built by Ionescu-Tulcea (Kernel.traj) from the synchronous lazy step kernels of Definition 1.2, started at σ₀; reason: the process is constructed from its definition (paper.md R4); every event and expectation of the paper is one of this law
--   - generalization: b as in Theorem 3.1 → any b > 0 with TwoOpinionBound b; reason: the Claim's proof uses only the conclusion of Theorem 3.1 for that b; the paper's b is an instance (paper.md R9)
--   - generalization: B a large constant to be determined later → every B > 0; reason: the Claim's proof uses no property of B; the paper's B = 4B′ is an instance (paper.md R9)
--   - reading: the hypotheses of Theorem 1.3, in which the phases t_1, …, t_{r_max} are defined → hphases: the partial sums of φ reach r_max, in place of Theorem 1.3's J < ∞; reason: the definition of ℓ_r for r ≤ r_max presupposes these minima exist, and the paper asserts t_{r_max} ≤ Δ_0 + ⋯ + Δ_J; this is all the Claim uses of J < ∞
--   - reading: κ, the number of opinions present in the model → |O(ξ_0)|, the number of opinions present at time 0; reason: the proof of Theorem 1.3 opens with 'Let κ be the number of opinions present in the model'
--   - encoding: a possible value H of H_{t_r} that determines R_α ≤ r < R_{α+1}; the values r_α, O_α → a path h with 0 < ℙ(ξ_s = h s, s ≤ t_r), R_α ω ≤ r < R_{α+1} ω for every ω in that event; r_α, O_α evaluated on h; reason: paper.md R7; h itself lies in the event, so its values are the determined ones
--   - encoding: ⌈·⌉ → Nat.ceil; reason: the argument is positive for b > 0
--   - encoding: a sequence of undirected graphs on a common vertex set V(G) with common degree d(v) → T : TemporalGraph V: a Fintype V, G t : SimpleGraph V, and the degree data d with degree_eq and one_le_d; reason: the paper's graphs are plain finite graphs (n vertices, m = ½ ∑ d(v) edges, e_t counts edges); no loop or parallel edge occurs in them, the self-loop of Figure 1 only pictures laziness
-- source:
--   Rocha Avila, Dell, Lapinskas, Temporal Conductance and Bounds on the Voter Model for Dynamic Networks, arXiv:2606.13374 (2 Nov 2026), proof of Theorem 1.3, Claim, p.25; definitions pp.24–25

import Mathlib
import Definitions.Def_TemporalVoter_TwoOpinionBound
import Definitions.Def_TemporalVoter_metaphaseIndex

open scoped ENNReal
open MeasureTheory ProbabilityTheory

namespace TemporalVoter

/-- **Claim in the proof of Theorem 1.3** (arXiv:2606.13374, version of 2 Nov 2026, p.25). Let `b > 0`
be a constant for which Theorem 3.1 holds and `B > 0`; consider the `k`-opinion voter model under
the hypotheses of Theorem 1.3, with phases `t_r` (`r ≤ r_max = ⌊Bm/d_min⌋`) and metaphase
boundaries `R_α` (p.24). Let `r, α ≥ 0`, let `H` be a possible value of `H_{t_r}` that determines
`R_α ≤ r < R_{α+1}`, and let `r_α`, `O_α` be the values of `R_α` and `O(t_{r_α})` it determines.
With `ξ_α := 1 + ⌈b(6m/(d_min|O_α|) + log(1 + 6m/|O_α|))⌉`,
`ℙ(R_{α+1} > r + ξ_α | H_{t_r} = H) ≤ 2/3`.

**Formalization Note** `hphases` says the phases `t_1, …, t_{r_max}` exist (the partial sums of `φ`
reach `r_max`), as the definition of the phases on p.24 presupposes. -/
theorem theorem_1_3_claim (b : ℝ) (hb_pos : 0 < b) (hb : TwoOpinionBound b) (B : ℝ) (hB : 0 < B)
    {V : Type} [Fintype V] (T : TemporalGraph V) (k : ℕ) (σ₀ : V → Fin k)
    (Δ : ℕ → ℕ) (φ : ℕ → ℝ) (hΔ : ∀ j, 1 ≤ Δ j) (hφ : ∀ j, 0 ≤ φ j ∧ φ j ≤ 1)
    (hcond : ∀ j, φ j ≤ intervalCond T (Iminus Δ j) (Iplus Δ j))
    (hphases : ∃ ℓ, (rmax T B : ℝ) ≤ ∑ j ∈ Finset.range ℓ, φ j)
    (r α : ℕ) (h : ℕ → V → Fin k)
    (hpos : 0 < voterLaw T k σ₀ (historyEvent (phaseStart Δ φ r) h))
    (hdet : ∀ ω ∈ historyEvent (phaseStart Δ φ r) h,
      metaphaseIndex T B Δ φ α ω ≤ r ∧ r < metaphaseIndex T B Δ φ (α + 1) ω) :
    (voterLaw T k σ₀)[|historyEvent (phaseStart Δ φ r) h]
        {ω | r + (1 + ⌈b * (6 * T.m /
            (T.dmin * ((opinionsPresent (h (phaseStart Δ φ (metaphaseIndex T B Δ φ α h)))).card : ℝ))
            + Real.log (1 + 6 * T.m /
              ((opinionsPresent (h (phaseStart Δ φ (metaphaseIndex T B Δ φ α h)))).card : ℝ)))⌉₊)
          < metaphaseIndex T B Δ φ (α + 1) ω} ≤ 2 / 3 := by sorry

end TemporalVoter
