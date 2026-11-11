-- Prove2me | Theorems.Thm_SumReLU_theorem_1_3
-- name    : SumReLU.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T08:27:42.654456+00:00
-- url     : https://prove2.me/theorems/95b97841-854b-4421-a606-5793061e560a
-- title:
--   Theorem 1.3 (with Theorem 5.1) — one learner with poly(d, k, 1/ε) samples and time reaching ‖h−f‖ ≤ ε‖f‖ and ‖h−f‖² ≤ ε w.p. 2/3
-- statement:
--   There is a randomized algorithm and a constant $C$ with the following guarantee. Given $d,k\ge1$, $\epsilon>0$ and access to independent examples $(x,f(x))$ with $x\sim N(0,I_d)$ and $f(x)=\sum_{i=1}^k\beta_i\sigma(w_i\cdot x)\in\mathcal C_{d,k}$ ($\beta_i\in[0,1]$, $\|w_i\|_2=1$), on every run it draws at most $C(d+k+1/\epsilon)^C$ examples and performs at most $C(d+k+1/\epsilon)^C$ operations, and with probability at least $2/3$ it outputs a hypothesis
--   $$
--   h(x)=g\cdot x+\sum_{j=1}^k\alpha_j\,|v_j\cdot x|,\qquad \alpha_j\ge0,
--   $$
--   such that
--   $$
--   \|h-f\|_{L^2}\le\epsilon\,\|f\|_{L^2}\qquad\text{and}\qquad \|h-f\|_{L^2}^2=\mathbb E_{(x,y)}\big[(y-h(x))^2\big]\le\epsilon ,
--   $$
--   with $\|g\|_{L^2}=(\mathbb E_{x\sim N(0,I_d)}[g(x)^2])^{1/2}$.
--
--   This is the paper's main result: positive linear combinations of $k$ ReLUs are learnable under Gaussian inputs with sample and computational complexity polynomial in $d$, $k$ and $1/\epsilon$, by a learner whose output is itself a small network.
--
--   **Formalization Note** The algorithm is a single program of the published randomized sampling real RAM `GaussMixHH.Machine`, restricted by `SelfSelReg.ArithmeticCoin` to exact $+,-,\times,\div$, rational literals, comparisons, memory and pointer moves, a pointer-to-real cast, fair coins, `sample` and `halt` (no square root, exponential, trigonometric function, eigensolver or Gaussian draw). One `sample` writes one labeled example $(x,f(x))\in\mathbb R^{d+1}$, label last, and costs $d+1$; every other instruction costs $1$. The program and the constant $C$ are fixed before every parameter and every target. The program reads $k,\epsilon$ from memory and the hypothesis is decoded from memory; the integrability of $(h-f)^2$ is asserted, so the $L^2$ norm is not a junk value.
--
--   Differences from the source:
--   - reading: "there is an algorithm … uses poly samples and time" → one program of the `GaussMixHH` sampling real RAM restricted by `SelfSelReg.ArithmeticCoin`; time is the number of executed instructions, `sample` costing $d+1$; reason: the paper names no machine; its algorithm uses exact eigenvectors, exponentials, tangents and Gaussian draws, and arithmetic with coins and sampling is the non-weaker reading of "time"
--   - generalization: $\epsilon\in(0,1)$ (Theorem 1.3) → every $\epsilon>0$; reason: Theorem 5.1's range; specializes to $\epsilon\in(0,1)$
--   - generalization: the relative clause $\|h-f\|_{L^2}\le\epsilon\|f\|_{L^2}$ (Theorem 1.3) or the absolute clause $\mathbb E[(y-\hat y)^2]\le\epsilon$ (Theorem 5.1) → both clauses for the same run; reason: the conjunction implies each printed version
--   - generalization: "outputs a hypothesis $h$" → $h(x)=g\cdot x+\sum_{j<k}\alpha_j|v_j\cdot x|$ with all $\alpha_j\ge0$; reason: the form the paper states for its hypothesis (p.2; Algorithm 1, lines 8–9); any hypothesis of this form is a hypothesis
--   - encoding: $\mathrm{poly}(d,k,1/\epsilon)$ samples and time → $C(d+k+1/\epsilon)^C$ on both, with one constant $C$ fixed with the program before $d,k,\epsilon,\beta,w$; reason: §2, p.9 defines $\mathrm{poly}(\cdot)$ by explicit constants
--   - reading: sample count and running time → worst-case bounds on every coin tape and example stream; reason: the stronger of the two readings (worst case, not expected)
--   - encoding: "with probability at least 2/3", independent examples, input and output → a measurable set of runs of measure at least $2/3$ under coins $\otimes$ i.i.d. examples of law $(x,f(x))$; input list $[k,\epsilon]$; hypothesis read from memory; integrability of $(h-f)^2$ asserted; reason: Lean conventions for the run space and the machine's input/output; $\|h-f\|_{L^2}^2=\mathbb E[(y-h(x))^2]$ because $y=f(x)$
-- source:
--   Diakonikolas, Diakonikolas, Wang, Zarifis, Learning Positive Linear Combinations of ReLUs in Fully Polynomial Time, arXiv:2610.32940 (PDF sha256 66803576…6c48), Theorem 1.3, p.2 (PDF p.4); Theorem 5.1, p.48 (PDF p.50); hypothesis form p.2 and Algorithm 1, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_GaussMixHH_Machine
import Definitions.Def_SelfSelReg_ArithmeticCoin
import Definitions.Def_SumReLU_reluSum
import Definitions.Def_SumReLU_gaussL2
import Definitions.Def_SumReLU_sampleLaw
import Definitions.Def_SumReLU_goalInput

open MeasureTheory ProbabilityTheory

namespace SumReLU

/-- **Theorem 1.3** (Main result), with the absolute error clause of its formal version Theorem 5.1.

Diakonikolas, Diakonikolas, Wang, Zarifis, *Learning Positive Linear Combinations of ReLUs in
Fully Polynomial Time*, arXiv:2610.32940 (PDF sha256 66803576…6c48), Theorem 1.3, p.2 (PDF p.4): "There is an algorithm that, given d, k ∈ ℤ₊, ϵ ∈ (0, 1), and access
to independent examples (x, f(x)), where x ∼ N(0, I_d) and f ∈ C_{d,k}, uses poly(d, k, 1/ϵ) samples
and time and outputs a hypothesis h such that, with probability at least 2/3, ‖h − f‖_{L2} ≤ ϵ‖f‖_{L2}."
Theorem 5.1, p.48 (PDF p.50): "Let d, k ∈ ℤ₊ and ϵ > 0. … with probability at least 2/3, it outputs a
hypothesis ŷ(x) satisfying E_{(x,y)∼D}[(y − ŷ(x))²] ≤ ϵ. LearnSumReLUs(d, k, ϵ; D) uses poly(d, k, 1/ϵ)
samples from D, and runs in poly(d, k, 1/ϵ) time." Hypothesis form, p.2: "h(x) = g · x +
∑_{i=1}^k α_i|v_i · x|", a positive combination (Algorithm 1, lines 8–9, p.12).

**Formalization Note.**
* The algorithm is one program `P` of the published sampling real RAM `GaussMixHH`, restricted by
  `SelfSelReg.ArithmeticCoin` to exact `+ − × ÷`, rational literals, comparisons, memory and pointer
  moves, a pointer-to-real cast, fair coins, `sample` and `halt` (no `√`, `exp`, `cos`, `sin`, no
  eigensolver, no Gaussian draw). `P` and the constant `C` are chosen before `d, k, ε, β, w`. `P`
  runs in dimension `d + 1`, receives `k, ε` in memory (`goalInput`) and `d + 1` in pointer `0`,
  and reaches `f` only through `sample`, which writes one example `(x, f(x))`, `x ∼ N(0, I_d)`
  (cost `d + 1`). Work counts executed instructions.
* `poly(d, k, 1/ϵ)`: the bound `C(d + k + 1/ε)^C` (`resourceBound`) on the number of samples
  **and** on the work, on **every** coin tape and example stream.
* "With probability at least 2/3": a measurable set of runs of `sampleSpace β w`-measure at least
  `2/3` on which every halted state decodes (`decodeHypothesis`) to `h(x) = g·x + ∑_j α_j|v_j·x|`
  with all `α_j ≥ 0` and **both** `‖h − f‖_{L²} ≤ ε‖f‖_{L²}` (Theorem 1.3) and
  `‖h − f‖²_{L²} = E[(y − h(x))²] ≤ ε` (Theorem 5.1), for every `ε > 0` (Theorem 5.1's range).
  The integrability of `(h − f)²` is asserted, so the `L²` norm is not a junk value. -/
theorem theorem_1_3 :
    ∃ (P : GaussMixHH.Program) (_ : GaussMixHH.Admissible P) (_ : SelfSelReg.ArithmeticCoin P)
      (C : ℕ),
      ∀ (d k : ℕ), 1 ≤ d → 1 ≤ k → ∀ ε : ℝ, 0 < ε →
      ∀ (β : Fin k → ℝ) (w : Fin k → EuclideanSpace ℝ (Fin d)), InClass β w →
        (∀ ω : (ℕ → Bool) × (ℕ → EuclideanSpace ℝ (Fin (d + 1))), ∃ t : ℕ,
          let s := GaussMixHH.run P (d + 1) (GaussMixHH.initState (d + 1) (goalInput k ε)) ω t
          s.halted = true ∧
            (s.samplesUsed : ℝ) ≤ resourceBound C d k ε ∧
            (s.work : ℝ) ≤ resourceBound C d k ε) ∧
        ∃ E : Set ((ℕ → Bool) × (ℕ → EuclideanSpace ℝ (Fin (d + 1)))), MeasurableSet E ∧
          ENNReal.ofReal (2 / 3) ≤ sampleSpace β w E ∧
          ∀ ω ∈ E, ∀ t : ℕ,
            let s := GaussMixHH.run P (d + 1) (GaussMixHH.initState (d + 1) (goalInput k ε)) ω t
            s.halted = true →
              let H := decodeHypothesis d k s
              (∀ j, 0 ≤ H.α j) ∧
                Integrable (fun x => (hypFun H x - reluSum β w x) ^ 2)
                  (stdGaussian (EuclideanSpace ℝ (Fin d))) ∧
                gaussL2 (fun x => hypFun H x - reluSum β w x) ≤ ε * gaussL2 (reluSum β w) ∧
                gaussL2 (fun x => hypFun H x - reluSum β w x) ^ 2 ≤ ε := by sorry

end SumReLU
