-- Prove2me | Theorems.Thm_QGradGAW_Smooth_theorem_21
-- name    : QGradGAW.Smooth.theorem_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:29:07.79688+00:00
-- url     : https://prove2.me/theorems/f56b609e-9921-4749-8864-bd83717b4a1b
-- title:
--   Theorem 21, pp. 26–27 — Jordan's algorithm with median amplification: Pr[‖g̃ − g‖∞ > ε] ≤ ρ from O(log(d/ρ)) queries
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. Let $c\in\mathbb R$, let $r,\rho,\varepsilon,M>0$ with $r,\rho,\varepsilon<M$, and let $y,g\in\mathbb R^d$ with $\|g\|_\infty\le M$. Put
--   $$n_\varepsilon=\Big\lceil\log_2\frac{4}{r\varepsilon}\Big\rceil,\qquad n_M=\big\lceil\log_2(3rM)\big\rceil,\qquad n=n_\varepsilon+n_M ,$$
--   and assume $n\ge0$. Suppose $f$ satisfies
--   $$\big|f(y+rx)-g\cdot rx-c\big|\le\frac{\varepsilon r}{8\cdot42\pi}$$
--   for all but a $1/1000$ fraction of the points $x\in G_n^d$. Run Algorithm 2 with $n$-qubit registers and the phase oracle $O:|x\rangle\mapsto e^{2\pi i\,2^{n_\varepsilon} f(y+rx)}|x\rangle$ (one query per run) $T$ times independently, with $T\ge C\log(d/\rho)$; read each outcome $k\in G_n^d$ as the estimate $(2^{n_M}/r)\,k$ and output the coordinate-wise median $\tilde g$. Then
--   $$\Pr\big[\|\tilde g-g\|_\infty>\varepsilon\big]\le\rho .$$
--
--   This is the query part of Theorem 21: $O(\log(d/\rho))$ queries to $O$ suffice to learn the gradient of a function that is close to affine on most of a hypergrid.
--
--   **Formalization Note** The number of queries is the number $T$ of runs, since Algorithm 2 calls its oracle once; "$O(\log(d/\rho))$ queries" is $T\ge C\log(d/\rho)$ with $C$ absolute and chosen before all parameters. In Algorithm 2 the oracle is $e^{2\pi i 2^n h}$ with $h(x)=f(y+rx)/2^{n_M}$, which is $O$ (proof of Theorem 21: $O=O_h^{2\pi N}$). $n_\varepsilon$ and $n_M$ are integers (possibly negative) and $2^{n_M}$ is an integer power; only the register size $n=n_\varepsilon+n_M$ must be a natural number, which the page leaves implicit. The gate-complexity claim is not formalized. The hypotheses $r,\rho,\varepsilon<M$ are kept as printed.
-- source:
--   Gilyén, Arunachalam, Wiebe, Optimizing quantum optimization algorithms via faster quantum gradient computation, arXiv:1711.00465v3, pp. 26–27, Theorem 21 (query statement) and its proof

import Mathlib
import Definitions.Def_QGradGAW_Smooth_Setting

namespace QGradGAW.Smooth

open QAlgorithms

/-- arXiv:1711.00465v3, pp. 26–27, Theorem 21 (query statement): there is an absolute constant
`C > 0` such that the following holds. Let `c ∈ ℝ`, `r, ρ, ε < M ∈ ℝ₊`, `y, g ∈ ℝ^d` with
`‖g‖∞ ≤ M`, `n_ε := ⌈log₂(4/(rε))⌉`, `n_M := ⌈log₂(3rM)⌉` and `n := n_ε + n_M` (a number of
qubits, so `n ≥ 0`). Suppose `|f(y + rx) − g · rx − c| ≤ εr/(8 · 42π)` for all but a `1/1000`
fraction of the points `x ∈ G_n^d`. Then `T ≥ C log(d/ρ)` independent runs of Algorithm 2 with
the oracle `|x⟩ ↦ e^{2πi 2^{n_ε} f(y + rx)}|x⟩` (one query each), each outcome `k` read as the
estimate `(2^{n_M}/r) k`, followed by the coordinate-wise median, output `g̃` with
`Pr[‖g̃ − g‖∞ > ε] ≤ ρ`. -/
theorem theorem_21 :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (c r ρ ε M : ℝ), 0 < r → 0 < ρ → 0 < ε → 0 < M →
      r < M → ρ < M → ε < M → ∀ y g : Fin d → ℝ, ‖g‖ ≤ M →
      ∀ (nε nM : ℤ) (n : ℕ), nε = ⌈Real.logb 2 (4 / (r * ε))⌉ →
        nM = ⌈Real.logb 2 (3 * r * M)⌉ → (n : ℤ) = nε + nM →
      ∀ f : (Fin d → ℝ) → ℝ,
        ((Finset.univ.filter fun x : Fin d → Qubits n =>
            ¬ |f (y + r • gridVec x) - ∑ i, g i * (r * gridVec x i) - c| ≤
              ε * r / (8 * 42 * Real.pi)).card : ℝ) ≤ (2 ^ n : ℝ) ^ d / 1000 →
      ∀ T : ℕ, C * Real.log (d / ρ) ≤ T →
        medianFailProb d n T (fun z => f (y + r • z) / (2 : ℝ) ^ nM)
          (fun k i => ((2 : ℝ) ^ nM / r) * gridPoint n (k i)) g ε ≤ ρ := by sorry

end QGradGAW.Smooth
