-- Prove2me | Theorems.Thm_QAlgorithms_Papers_GAW19_gradient_phaseQueries
-- name    : QAlgorithms.Papers.GAW19.gradient_phaseQueries
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T18:48:38.978522+00:00
-- url     : https://prove2.me/theorems/d86c35c5-3adf-4432-b372-9f8177ef1c73
-- title:
--   GAW Theorem 23: gradient estimation with higher-order central differences and phase queries
-- statement:
--   This is the higher-order gradient algorithm of Gilyén–Arunachalam–Wiebe (Theorem 23).
--
--   Let $f : [-R,R]^d\to\mathbb R$ be accessed through fractional phase queries: for a finite set of query points $X\subseteq[-R,R]^d$ chosen by the algorithm, and every $r\in[-1,1]$, a unitary $O_f^r$ with $O_f^r|x\rangle|0\rangle=e^{irf(x)}|x\rangle|0\rangle$ for $x\in X$; each application of some $O_f^r$ counts as one query. For $x\ne0$ write $\partial_r^{k}f(x)=\frac{d^k}{d\tau^k}f(x+\tau r)\big|_{\tau=0}$ (taken within the cube) with $r=x/\|x\|$, $\|\cdot\|$ the Euclidean norm.
--
--   There is an absolute constant $C>0$ such that for all $d$, $m\in\mathbb Z_+$, $R>0$, $B\ge0$, $\varepsilon>0$, $\rho\in(0,1)$ and every a-priori gradient bound $M>0$ there is a quantum algorithm (query points, start state, circuit and classical post-processing of the final measurement, all independent of $f$) using at most
--   $$C\left(\max\left(\frac{\sqrt d}{\varepsilon}\Big(\frac{B\sqrt d}{\varepsilon}\Big)^{1/(2m)},\ \frac{m}{\varepsilon R}\right)\log(2m)+m\right)\big(1+\log(d/\rho)\big)$$
--   phase queries with the following property: for every $f$ that is $(2m+1)$-times differentiable on $[-R,R]^d$, satisfies $|\partial_r^{2m+1}f(x)|\le B$ for all $x\in[-R,R]^d\setminus\{0\}$, $r=x/\|x\|$, and $\|\nabla f(0)\|_\infty\le M$, and for every fractional phase oracle for $f$, the output $g$ satisfies
--   $$\Pr\big[\|g-\nabla f(0)\|_\infty\le\varepsilon\big]\ge1-\rho .$$
--
--   The bound shows that higher-degree central difference formulas reduce the query cost of Jordan's gradient algorithm, exponentially in $d$ for low-degree polynomials.
--
--   **Formalization Note** The known gradient bound $M$ is the hypothesis of Theorem 21 that the proof uses (the query count is independent of $M$). The factor $\log(d/\rho)$ is written $1+\log(d/\rho)$, the proof's repetition count $\lceil C\log(d/\rho)\rceil\ge1$. Queries are uncontrolled and non-adjoint, as the proof applies them.
-- source:
--   Optimizing quantum optimization algorithms via faster quantum gradient computation (Gilyén, Arunachalam, Wiebe), arXiv:1711.00465v3, Theorem 23, PDF p. 28. https://arxiv.org/abs/1711.00465v3 . PDF SHA-256: 4b76edbf6d3c29bbb48102f8108e19d938981759540f741e091370c9817c4e63.

import Definitions.Def_QAlgorithms_Defs_PhaseOracles
set_option autoImplicit false

namespace QAlgorithms.Papers.GAW19

universe u



/-- GAW p.28, Theorem 23 (gradient estimation with phase queries). Let `m ∈ ℤ₊`, `R > 0`,
`B ≥ 0`, and let `f : [−R, R]^d → ℝ` be given with (fractional) phase oracle access. If `f` is
`(2m + 1)`-times differentiable and `|∂_r^{2m+1} f(x)| ≤ B` for all `x ∈ [−R, R]^d`, `r = x/‖x‖`,
then an approximate gradient `g` with `‖g − ∇f(0)‖_∞ ≤ ε` is computed with probability at least
`1 − ρ` using
`O((max(√d/ε · (B√d/ε)^{1/(2m)}, m/(εR)) log(2m) + m) log(d/ρ))` phase queries.

Model: the algorithm chooses finitely many distinct query points `pt j ∈ [−R, R]^d`, a start
state, a circuit of uncontrolled, non-adjoint fractional queries `O^r_f`, `r ∈ [−1, 1]` (each one
query, eq. (25) p.30), and a classical post-processing `out` of the final computational-basis
measurement; all of this before `f` and the oracle. Pinned readings (recorded in STATUS.md):
the algorithm is built for a known bound `‖∇f(0)‖_∞ ≤ M` (Theorem 21, p.26, which the proof
uses; the query count is `M`-independent), and the factor `log(d/ρ)` is read as
`1 + log(d/ρ)` (the proof repeats `⌈C log(d/ρ)⌉ ≥ 1` times). "(2m + 1)-times differentiable" is
differentiability within the cube of the derivatives of order `≤ 2m`; the directional
derivative is taken within the cube along the ray (Definition 6, p.12), for `x ≠ 0`. -/
theorem gradient_phaseQueries :
    ∃ C : ℝ, 0 < C ∧ ∀ (d m : ℕ), 1 ≤ m → ∀ R B ε ρ M : ℝ, 0 < R → 0 ≤ B → 0 < ε →
      0 < ρ → ρ < 1 → 0 < M → ∀ w : ℕ,
        ∃ (N : ℕ) (pt : Fin N → Fin d → ℝ), Function.Injective pt ∧
          (∀ j, pt j ∈ Set.univ.pi fun _ : Fin d => Set.Icc (-R) R) ∧
          ∃ (a : ℕ) (c : PhaseQueryCircuit (Fin N) (Set.Icc (-1 : ℝ) 1) w a)
            (ψ0 : EuclideanSpace ℂ (Fin N × Qubits (w + a)))
            (out : Fin N × Qubits (w + a) → Fin d → ℝ),
            ‖ψ0‖ = 1 ∧
            (∀ s ∈ c, ∀ (r : Set.Icc (-1 : ℝ) 1) (adj : Bool) (b : Option (Fin a)),
              s = .query r adj b → adj = false ∧ b = none) ∧
            (c.queryCount : ℝ) ≤ C * ((max (Real.sqrt d / ε * (B * Real.sqrt d / ε) ^ (1 / (2 * (m : ℝ))))
                (m / (ε * R)) * Real.log (2 * m) + m) * (1 + Real.log (d / ρ))) ∧
            ∀ f : (Fin d → ℝ) → ℝ,
              (∀ j < 2 * m + 1, DifferentiableOn ℝ
                (iteratedFDerivWithin ℝ j f (Set.univ.pi fun _ : Fin d => Set.Icc (-R) R))
                (Set.univ.pi fun _ : Fin d => Set.Icc (-R) R)) →
              (∀ x ∈ Set.univ.pi (fun _ : Fin d => Set.Icc (-R) R), x ≠ 0 →
                |rayDeriv (2 * m + 1) f (Set.univ.pi fun _ : Fin d => Set.Icc (-R) R) x
                  ((euclidNorm x)⁻¹ • x)| ≤ B) →
              ‖(fun i => fderiv ℝ f 0 (Pi.single i 1) : Fin d → ℝ)‖ ≤ M →
              ∀ O : Set.Icc (-1 : ℝ) 1 → Matrix (Fin N × Qubits w) (Fin N × Qubits w) ℂ,
                IsGAWFractionalOracle (fun _ => false) O (fun j => f (pt j)) →
                probEvent (act (c.unitary O) ψ0)
                  (fun z => ‖out z - fun i => fderiv ℝ f 0 (Pi.single i 1)‖ ≤ ε) ≥ 1 - ρ := by
  sorry


end QAlgorithms.Papers.GAW19
