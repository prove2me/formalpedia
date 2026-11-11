-- Prove2me | Theorems.Thm_QuadStatRE_Main_theorem_5_2
-- name    : QuadStatRE.Main.theorem_5_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:48:01.803812+00:00
-- url     : https://prove2.me/theorems/2ccc53ec-a189-4ace-8bf7-631834d55e00
-- title:
--   Theorem 5.2 — privacy amplification: τ_{4+k} ≤ (1/10)(41/100)^{3^k/2} and SD(Enc_{4+k,t}(v), Sim_{4+k,t}(f(v))) ≤ ½·2^{−3^k/4}
-- statement:
--   Let $\mathrm{Enc}_{r,t}$ be the depth-$r$ iterated encoder of $f(x,y,z,w)=xyz+w$ with the basic gadget $\mathrm{Enc}_t$ at the leaves, $\mathrm{Sim}_{r,t}$ its natural simulator (given $b$, choose $(x,y,z)$ uniformly, set $w=b+xyz$ and run $\mathrm{Enc}_{r,t}$), and $\tau_r$ the normalized $\chi^2$-information of the iterated equality leakage $W_r$. For every $k\ge0$,
--   $$\tau_{4+k}\le\frac1{10}\Big(\frac{41}{100}\Big)^{3^k/2}, \tag{5.3}$$
--   and consequently, for every input $v\in\mathbb F_2^4$ and every integer $t\ge1$,
--   $$\mathrm{SD}\big(\mathrm{Enc}_{4+k,t}(v),\ \mathrm{Sim}_{4+k,t}(f(v))\big)\le\frac12\,2^{-3^k/4}. \tag{5.4}$$
--
--   This is the privacy half of the degree-two encoding of $xyz+w$; with Lemmas 3.1 and 4.3 for correctness it gives Corollary 5.4 and, through the reductions of [AIK06b], the main theorem.
--
--   **Formalization Note.** Powers with real exponents are `Real.rpow`. The encodings are compared as the laws of their outputs under uniform tapes; the simulator's coins are the uniform triple and a uniform encoder tape.
--
--   Differences from the source:
--
--   - encoding: Enc_{4+k,t}(v) and Sim_{4+k,t}(f(v)) as random variables → law of encR (4 + k) t on a uniform tape, law of simR (4 + k) t (f v) on uniform coins (s, tape); reason: output distributions of randomized algorithms
--   - encoding: the exponents 3^k/2 and −3^k/4 → real powers (Real.rpow); reason: the same real numbers
--   - encoding: bits {0,1} and F₂ → ZMod 2; reason: the same field
-- source:
--   Applebaum, Quadratic Statistical Randomized Encoding for All Functions, STOC 2027 submission (manuscript sha256 000cbf4e…), pp. 25–26, Theorem 5.2, (5.3)–(5.4)

import Mathlib
import Definitions.Def_QuadraticRE_SD
import Definitions.Def_QuadStatRE_Main_ChiSquare
import Definitions.Def_QuadStatRE_Main_Iterated
open QuadraticRE

namespace QuadStatRE.Main

/-- Theorem 5.2 (Privacy amplification), pp. 25–26: for every `k ≥ 0`,
`τ_{4+k} ≤ (1/10)(41/100)^{3^k/2}` (5.3); consequently, for every input `v` and every integer `t ≥ 1`,
`SD(Enc_{4+k,t}(v), Sim_{4+k,t}(f(v))) ≤ (1/2) 2^{−3^k/4}` (5.4). -/
theorem theorem_5_2 :
    (∀ k : ℕ, tau (Wr (4 + k)) ≤ 1 / 10 * (41 / 100 : ℝ) ^ ((3 : ℝ) ^ k / 2)) ∧
    (∀ k t : ℕ, 1 ≤ t → ∀ v : Fin 4 → F2,
      SD (law ((encR (4 + k) t).desc.eval v)) (law (simR (4 + k) t (targetF v)))
        ≤ 1 / 2 * (2 : ℝ) ^ (-((3 : ℝ) ^ k / 4))) := by sorry

end QuadStatRE.Main
