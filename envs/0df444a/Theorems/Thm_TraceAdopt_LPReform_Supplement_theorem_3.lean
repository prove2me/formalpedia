-- Prove2me | Theorems.Thm_TraceAdopt_LPReform_Supplement_theorem_3
-- name    : TraceAdopt.LPReform.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T05:52:32.391684+00:00
-- url     : https://prove2.me/theorems/53c54b5b-42bf-4de3-9679-606fe570d2b4
-- title:
--   Theorem 3, p. 47 — exact weighted diffusion dynamic programming in $[\vartheta_{\max}\omega]^{O(\omega)}(n+m)$ time
-- statement:
--   Let $G$ be the finite hypergraph of §3, with $n$ firms and $m$ supply chains, integral nonnegative incidence benefits $r_{ji}$, positive integral adoption costs $c_i$ and integral thresholds $2\le\theta_j\le|e_j|$. Assume connectedness and that every firm can receive enough total benefit, as in the published standing assumptions. Let $w_i\in\mathbb R$ be arbitrary seeding costs and let the hypergraph tree-width be at most $\omega$. Write
--
--   $$\vartheta_{\max}=\max\{\max_i c_i,\max_j(\theta_j-1)\}.$$
--
--   **Theorem 3.** One absolute constant $C>0$ and one fixed program, independent of every network, width and cost vector, suffice to construct a nice auxiliary decomposition, evaluate the weighted residual-demand dynamic program and reconstruct a firm seed set $S_0$ satisfying
--
--   $$S_\infty=N_F,\qquad\sum_{i\in S_0}w_i=\mathrm{OPT},$$
--
--   within
--
--   $$C\big((\vartheta_{\max}+1)(\omega+2)\big)^{C(\omega+1)}(n+m+1)$$
--
--   charged instructions. Preparation, table evaluation and backpointer reconstruction are part of the same run. This is the paper's $[\vartheta_{\max}\omega]^{O(\omega)}(n+m)$ bound with explicit absolute constants.
--
--   This gives the exact dynamic-programming counterpart to the published LP reformulation. It covers the full weighted model, without uniform-chain, unit-benefit, unit-adoption-cost, nonnegative-seeding-cost or supplied-decomposition restrictions.
--
--   **Formalization Note** `DynamicProgram` fixes the finite leaf/replace/join recurrence, explicit infeasibility, deterministic ties, stored costs/backpointers, memory layout and trace checkpoints. The program receives only the instance and costs, prepares a nice auxiliary decomposition of width at most a constant times $\omega+1$, writes all recurrence tables in postorder, and reconstructs the selected seed set in final memory. Comparisons and memory operations are charged; the oracle returns zero. This is an unproved mission target, including existence of the uniform implementation and its preparation-time bound; neither is assumed as a hypothesis.
--
--   Differences from the source:
--   - encoding: via a dynamic program → the finite residual-demand recurrence dpEvaluate, stored costs/backpointers and actual RAM configurations realizing every table and reconstructing the seed set; reason: states the algorithm and its charged implementation, not merely a nonconstructive optimum
--   - encoding: Algorithm 2 threshold vectors, simultaneous ranks and set-valued entries → actual thresholds minus earlier-subtree incoming weight; distinct ranks; a firm-seed mask; optional cost/backpointer entries; saturated join correction and subtraction of boundary seed cost; reason: implements the existential Theorem 3 on the full weighted signed-cost domain; boundary seeds must agree for local union costs, and infeasibility must not be represented by the all-firm sentinel; no instance is excluded
--   - encoding: treewidth tw(G) = omega → HypTreewidthLE I omega; the program constructs a nice auxiliary decomposition of width q <= C*(omega+1) and O((q+1)*(n+m+1)) bags during its run; reason: a monotone width bound and constant-factor width approximation preserve the O(omega) exponent and linear size factor; no decomposition is supplied
--   - encoding: [vartheta_max * omega]^{O(omega)}(n+m) time → one C>0 and one finite RAM program before every input, at most C*((varthetaMax+1)*(omega+2))^(C*(omega+1))*(n+m+1) executed instructions for preparation, table evaluation and reconstruction together; reason: explicit uniform constants in the arithmetic/comparison model; shifts preserve the asymptotic class and define boundary values
--   - reading: hypergraph as defined in Section 3 and seeding costs w_i → the immutable published Instance.Standing and arbitrary real costs; a fully activating output of cost OPT; reason: retains connectedness WLOG, positive integral adoption costs, integral benefits and feasible chain thresholds; adds no nonnegative-cost or finite-precision premise
-- source:
--   Blaettchen, Calmon & Hall, Traceability Technology Adoption in Supply Chain Networks, arXiv:2104.14818v4, p. 47, Theorem 3 (proof p. 47; Algorithm 2 p. 44; Lemmas 2–3 pp. 43–47; Definition 5 p. 42)

import Mathlib
import Definitions.Def_TraceAdopt_LPReform_Supplement_DynamicProgram

set_option autoImplicit false

namespace TraceAdopt.LPReform.Supplement

open MeanCertificates1424.Hardness.Supplement

/-- Theorem 3, p. 47. One uniform oracle-free RAM program prepares a nice decomposition,
evaluates the residual-demand leaf/replace/join recurrence, and reconstructs an optimal
firm seed set through the stored backpointers. Every preparation, table and reconstruction
instruction is charged to the same bound. A constant-factor width approximation suffices;
no decomposition, width parameter or numerical comparison oracle is supplied as input. -/
theorem theorem_3 :
    ∃ (C : ℕ) (P : Program), 0 < C ∧
      ∀ (I : Instance) (ω : ℕ) (w : Fin I.n → ℝ),
        I.Standing → HypTreewidthLE I ω →
        ∃ (q : ℕ) (D : NiceDecomposition I) (fin : Cfg),
          IsNiceDecomposition D q ∧ q ≤ C * (ω + 1) ∧
          D.N ≤ C * (q + 1) * (I.n + I.m + 1) ∧
          RealizesDiffusionDP P I w D q (dpTimeBound C I ω) fin ∧
          FullyActivates I (outSeeds I.n fin) ∧
          ∑ i ∈ outSeeds I.n fin, w i = OPT I w := by sorry

end TraceAdopt.LPReform.Supplement
