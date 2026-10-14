-- Prove2me | Theorems.Thm_PigeonholeDesign_Upper_lemma_EC_4
-- name    : PigeonholeDesign.Upper.lemma_EC_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:12:30.918445+00:00
-- url     : https://prove2.me/theorems/ae01350f-3541-488d-a756-a05b342982fb
-- title:
--   Lemma EC.4 (corrected constant) — on x* = (0,…,0,1,…,1), ALG^C(x*) = √T/√(2π) + O(T^{−1/2})
-- statement:
--   Let $T\ge2$ be even and let $x^*\in[0,1]^T$ be the arrival instance $(0,\dots,0,1,\dots,1)$ consisting of $T/2$ zeros followed by $T/2$ ones. There is a constant $C$, independent of $T$, such that the expected discrepancy of the completely randomized design on $x^*$ satisfies
--   $$\Bigl|\mathrm{ALG}^{\mathsf C}(x^*)-\frac{\sqrt T}{\sqrt{2\pi}}\Bigr|\ \le\ \frac{C}{\sqrt T},\qquad\text{i.e.}\qquad \mathrm{ALG}^{\mathsf C}(x^*)=\frac{1}{\sqrt{2\pi}}\sqrt T+O\bigl(T^{-1/2}\bigr).$$
--
--   This instance witnesses the $\Omega(T^{1/2})$ half of Lemma 2: the completely randomized design pays order $\sqrt T$ even on two-point data.
--
--   **Formalization Note** The paper prints the leading constant $1/\sqrt\pi$. Its proof treats the number $H$ of zeros placed in control as $\mathrm{Bin}(T/2,1/2)$, but under the completely randomized design $H$ is hypergeometric (population $T$, $T/2$ zeros, $T/2$ draws), with variance $T^2/(16(T-1))\approx T/16$; the discrepancy is $|2H-T/2|$, whose mean is $\sqrt T/\sqrt{2\pi}+O(T^{-1/2})$. Exact values of $\mathrm{ALG}^{\mathsf C}(x^*)/\sqrt T$ are $0.3637, 0.3807, 0.3943, 0.3987$ at $T=8,16,64,1024$, tending to $1/\sqrt{2\pi}\approx0.3989$, not $1/\sqrt\pi\approx0.5642$. The statement here carries the corrected constant. Subjects are indexed from $0$, so $x^*_t=0$ for $t<T/2$.
-- source:
--   Zhao and Zhou, Pigeonhole Design: Balancing Sequential Experiments from an Online Matching Perspective, arXiv:2201.12936v6, p. ec4 (PDF p. 42), Lemma EC.4 (constant corrected from 1/√π to 1/√(2π))

import Mathlib
import Definitions.Def_PigeonholeDesign_Upper_Setting

namespace PigeonholeDesign.Upper

theorem lemma_EC_4 :
    ∃ C : ℝ, ∀ T : ℕ, 2 ≤ T → Even T →
      |crdExp (fun t : Fin T => if (t : ℕ) < T / 2 then (0 : ℝ) else 1)
          - Real.sqrt T / Real.sqrt (2 * Real.pi)| ≤ C / Real.sqrt T := by sorry

end PigeonholeDesign.Upper
