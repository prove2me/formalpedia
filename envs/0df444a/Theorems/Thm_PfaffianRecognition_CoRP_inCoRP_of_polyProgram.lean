-- Prove2me | Theorems.Thm_PfaffianRecognition_CoRP_inCoRP_of_polyProgram
-- name    : PfaffianRecognition.CoRP.inCoRP_of_polyProgram
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-22T21:25:03.792819+00:00
-- url     : https://prove2.me/theorems/348d4c04-9c69-4550-8cac-c22b17c342e0
-- title:
--   coRP from a polynomial-time deterministic program on (random bits, input)
-- statement:
--   A one-sided randomized algorithm given as a deterministic polynomial-time program on (random string, input) yields membership in coRP.
--
--   Let $L$ be a language of bit strings and let $A(\rho,w)\in\{0,1\}$ be computed by a polynomial-time Boolean-stack Turing program reading the pair $(\rho,w)$. Fix $r\in\mathbb N$ and write $R(w)=(|w|+2)^r$. Suppose that
--
--   1. for every $w\in L$ and every $\rho\in\{0,1\}^{R(w)}$ we have $A(\rho,w)=1$, and
--   2. for every $w\notin L$, a uniformly random $\rho\in\{0,1\}^{R(w)}$ satisfies $\Pr_\rho[A(\rho,w)=0]\ge\tfrac12$.
--
--   Then $L\in\mathrm{coRP}$ in the execution-based sense of the mission: there is one fair-coin machine $M$ and constants $C\ge1$, $k$ such that on every input $w$ and every fair tape of length $B=C(|w|+2)^k$ the machine halts within $B$ steps with a single output bit, using at most $B$ tape bits; it always accepts $w\in L$ and rejects $w\notin L$ with probability at least $\tfrac12$.
--
--   This separates the machine-level definition of coRP from the algorithmic content: a randomized algorithm only needs to be written as a deterministic polynomial-time function of its random bits.
--
--   **Formalization Note** The program is a `PolyProgram` of the Boolean-stack machine library, reading `encodePair id id (ρ, w)` and writing `encodeBool`. The constructed coin machine first writes $R(w)$ in unary, then copies that many coin bits into the program's input.
-- source:
--   Priyanshu Pant, Ranveer Singh, Pfaffian Recognition is in coRP, STOC 2027 submission #858 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/858.pdf, definition of coRP (p. 3) and proof of Theorem 1.1 (p. 8): one randomized polynomial bit-time algorithm with perfect completeness

import Definitions.Def_PfaffianRecognition_Recognition_computation_model
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime

namespace PfaffianRecognition.CoRP

open OAI.MetricKMedian.Binary in
theorem inCoRP_of_polyProgram (L : List Bool → Prop)
    (A : List Bool × List Bool → Bool)
    (hA : Nonempty (PolyProgram (encodePair id id) encodeBool A)) (r : ℕ)
    (hyes : ∀ w, L w → ∀ ρ : List Bool, ρ.length = (w.length + 2) ^ r → A (ρ, w) = true)
    (hno : ∀ w, ¬ L w → (1 / 2 : ℝ) ≤ HypergraphUnreliability.FPRAS.fairProb ((w.length + 2) ^ r)
        (fun ω => A (HypergraphUnreliability.FPRAS.tapeList ω, w) = false)) :
    PfaffianRecognition.Recognition.InCoRP L := by sorry

end PfaffianRecognition.CoRP
