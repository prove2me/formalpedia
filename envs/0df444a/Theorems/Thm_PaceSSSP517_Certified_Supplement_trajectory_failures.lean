-- Prove2me | Theorems.Thm_PaceSSSP517_Certified_Supplement_trajectory_failures
-- name    : PaceSSSP517.Certified.Supplement.trajectory_failures
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:35:36.836207+00:00
-- url     : https://prove2.me/theorems/7cf1b678-0765-40c2-b9de-8025da3076af
-- title:
--   Theorem 3.11 — Trajectory-dependent failure count
-- statement:
--   Use the same graph, source, spanner and standing PACE parameters as Theorem 3.7, and any supported executed prefix. For every $1\le R$ in that prefix, let $\rho_R^\star$ be the maximum violating fraction among non-bulk rounds up to $R$. When such a round exists, put
--   $$
--   f_R^\star(\rho_R^\star)=
--   \left\lceil\frac{\ln(2Q^{(R+1)}/s)}
--   {\ln(1+\varepsilon/(10k\rho_R^\star))}\right\rceil\in\mathbb Z;
--   $$
--   otherwise put the evaluated climb length equal to zero. Here $Q^{(R+1)}$ is the actual reconstructed potential including round $R$'s virtual multiplier.
--
--   Every edge fails in at most $f_R^\star(\rho_R^\star)$ non-bulk rounds among the first $R$, and at most one bulk round. Deterministically,
--   $$
--   \kappa_{[R]}\le\frac{(2k-1)(f_R^\star(\rho_R^\star)+1)}{R}.
--   $$
--   If
--   $$
--   R\ge (2k/\varepsilon)(f_R^\star(\rho_R^\star)+1),
--   $$
--   round $R$'s stop flag is set, the actual execution is stopped, and its length is at most $R$. This applies to every qualifying executed round, hence to the first.
--
--   The companion theorem bounds failures using the observed trajectory. It uses the base failure and potential mechanisms, Lemmas 3.1 and 3.5 (ids a30c6d5b-1d2e-4b3d-92a6-cfd0d670b856 and b92177bc-c841-45a8-be36-4c6cf9284c1d). No probabilistic premise or potential upper bound is assumed.
--
--   Differences from the source:
--   - encoding: finite connected positive-real weighted undirected graph and finite profiles → published graph and Algorithm 1 modules with Fin n vertices and one stored orientation per edge; reason: canonical storage permits walks and the Bellman–Ford operator to use both orientations; connected spanners make every asserted real distance finite
--   - generalization: H computed by the upstream spanner routine → any H satisfying the same (2k−1+ε) all-pairs spanner condition; reason: the added results have no space clause and use only this condition; the prescribed routine output is an instance
--   - encoding: deterministically on the actual PACE execution → every SampleTrace whose trajectory equals its executed prefix, using one-based executed indices; reason: SampleTrace is the support restriction of the conditional Bernoulli choices including probability-one and probability-zero edges; unsupported samples are excluded
--   - reading: maximum violating fraction over non-bulk rounds without an empty-set convention → evaluated climb length is zero when there is no non-bulk round; reason: the maximum is empty in already-exact/all-bulk executions; the source maximum is undefined on this empty set; the explicit zero extension records zero non-bulk failures without inventing a positive rho
--   - encoding: ceil of the logarithm ratio and stop by the first qualifying round → integer ceiling with actual Q^(R+1), and the stop flag at every positive executed R satisfying the threshold; reason: the integer ceiling avoids truncating a potentially negative formula; pointwise stopping at every qualifying executed round implies stopping by the first such round
-- source:
--   Sarwan Ali, STOC 2027 submission #517 (October 2026), p. 9, Theorem 3.11; proof A.9, p. 20

import Definitions.Def_PaceSSSP517_Certified_Supplement_TraceStatistics

set_option autoImplicit false

namespace PaceSSSP517.Certified.Supplement

/-- Theorem 3.11, p.9, display (2); proof A.9 p.20. Counts are compared in
integers to preserve the source's signed ceiling. The empty non-bulk maximum
has climb length zero. Every R is a positive, executed round. -/
theorem trajectory_failures
    (n k : ℕ) (ε : ℝ) (G : WeightedGraph n) (H : Finset (Edge n)) (s₀ : Fin n)
    (hparams : Parameters n k ε) (hG : Connected G.edges)
    (hH : IsSpanner G H (2 * (k : ℝ) - 1 + ε))
    (Fs : List (Finset (Edge n))) (hFs : SampleTrace G H s₀ k ε Fs)
    (hexecuted : execution (trajectory G H s₀ k ε Fs).rounds =
      (trajectory G H s₀ k ε Fs).rounds) :
    let ts := (trajectory G H s₀ k ε Fs).rounds
    ∀ R ∈ past ts.length,
      let f := climbLength G ts k ε R
      (∀ e ∈ G.edges,
        ((failureRounds G ts (nonBulkRounds ts R) e).card : ℤ) ≤ f ∧
        (failureRounds G ts (bulkRounds ts R) e).card ≤ 1) ∧
      kappa G ts (past R) ≤ (2 * (k : ℝ) - 1) * ((f : ℝ) + 1) / (R : ℝ) ∧
      ((2 * (k : ℝ) / ε) * ((f : ℝ) + 1) ≤ (R : ℝ) →
        (roundAt ts R).stopping = true ∧ stopped ts ∧ ts.length ≤ R) := by sorry

end PaceSSSP517.Certified.Supplement
