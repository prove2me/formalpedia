-- Prove2me | Theorems.Thm_SketchAttr_LOO_Supplement_theorem_A_1
-- name    : SketchAttr.LOO.Supplement.theorem_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:54:49.604788+00:00
-- url     : https://prove2.me/theorems/5cd3af85-4ce2-4d63-aedd-2f4f309925f8
-- title:
--   Theorem A.1 — forward-only sketch baseline
-- statement:
--   One finite program and one universal constant $C>0$ work for every $n\ge1$, every scalar arithmetic circuit $\phi:\mathbb C^n\to\mathbb C$ real-valued on $[0,1]^n$, every $\varepsilon,\delta\in(0,1)$, and every stability profile $\alpha$ with $\phi$ $\alpha$-stable and $\alpha(4)<\infty$. With $N,\ell,m,k$ and the forward-only estimates defined above, the returned cells satisfy
--
--   $$\max_{i\in[n]}|\widehat L_i-\phi(e_i)|\le\varepsilon\alpha(4)$$
--
--   with probability at least $1-\delta$ under the published independent complex Gaussian tape law. On every tape the program halts without fault, consumes exactly $nm$ tape entries, and returns the specified full forward-only estimates. It makes no oracle calls.
--
--   The paper writes $\widetilde O(\operatorname{size}(\phi)\log(n/\delta)/\varepsilon^2)$ operations and $\widetilde O(\operatorname{size}(\phi)+n\log(n/\delta)/\varepsilon^2)$ auxiliary space; the forward-differentiation and trimmed-mean estimates on pp. 4–5, 12–13 yield the explicit forms
--
--   $$\text{steps}\le C\operatorname{size}(\phi)mN\log(N+1),\qquad
--   \text{space}\le C(\operatorname{size}(\phi)N+nmN),$$
--
--   where $N=\lceil\log_4(1/\varepsilon)\rceil$, $\ell=\log(16nN/\delta)$, $m=\lceil256\ell/\varepsilon^2\rceil$, and $k=\lfloor\ell\rfloor$. All coefficient arithmetic, powers, factorial scaling, selection and summation are charged using the published RAM instructions. The statement asserts these actual execution bounds rather than assuming a fast coefficient primitive.
--
--   This companion theorem supplies the forward-only comparison to the published goal's faster estimator.
--
--   Differences from the source:
--   - encoding: indices in [n] → indices in Fin n; reason: zero-based coordinate labels change no instance
--   - encoding: forward sketches with tilde O work and auxiliary-space bounds → N=ceil(log4(1/epsilon)), ell=log(16nN/delta), m=ceil(256ell/epsilon squared), k=floor(ell), and universal-C bounds C size m N log(N+1) and C(size N+nmN); reason: these are the full forward-only construction and constants from the source estimates; log(N+1) retains the published N=1 convention
--   - encoding: forward-sketch outputs with success probability at least 1-delta → a finite program returns the scalar full-sketch estimator on every tape and its simultaneous bad-event probability is at most delta; reason: the explicit execution and complementary event have the same accuracy and resource content
--   - encoding: independent complex Gaussian directions reused across coordinates and degrees → disjoint length-n blocks of the published complex Gaussian tape, exactly nm sampled entries, and no call instruction; reason: this supplies the same independent directions without backward-forward slices or exact high-variance corrections
-- source:
--   Chris Liaw, Aranyak Mehta, Grigoris Velegkas, Felix Zhou, Sketching Language Models for Context Attribution, STOC 2027 submission #9 (October 2026), PDF sha256 86af2569e45c55b1009e7453d4f53047b5820d44868a7f528bdb6fed1a2ef0e2, p. 28, Theorem A.1; Section 2.1, pp. 4–5; Propositions 4.4 and 4.8, pp. 12–13

import Mathlib
import Definitions.Def_SketchAttr_LOO_Supplement_Forward

open MeasureTheory
open scoped ENNReal

namespace SketchAttr.LOO.Supplement

theorem theorem_A_1 :
    ∃ (M : Program) (C : ℝ), 0 < C ∧
      (∀ j : ℕ, M[j]? ≠ some Instruction.call) ∧
      ∀ (n : ℕ), 1 ≤ n → ∀ (c : Circuit n 1) (ε δ : ℝ),
        0 < ε → ε < 1 → 0 < δ → δ < 1 → c.RealOnCube →
      ∀ α : StabilityProfile, IsStable (circuitFunction c) α →
        α ⟨4, by norm_num⟩ < ⊤ →
      (∀ tape : ℕ → ℂ,
        let fuel := forwardFuel C c ε δ
        let result := forwardRun M c ε δ tape fuel
        result.halted = true ∧ result.fault = false ∧
        result.cursor = n * forwardSamples n ε δ ∧
        (∀ i : Fin n, result.cm 0 i.val = forwardEstimate c ε δ tape i) ∧
        (fuel : ℝ) ≤ C * forwardWorkScale c ε δ ∧
        (∀ t : ℕ, t ≤ fuel →
          ((forwardRun M c ε δ tape t).space : ℝ) ≤ C * forwardSpaceScale c ε δ)) ∧
      (gaussianTape (forwardFailure M C c ε δ α) ≤ ENNReal.ofReal δ) := by sorry

end SketchAttr.LOO.Supplement
