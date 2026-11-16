-- Prove2me | Theorems.Thm_PolyEulerFlow_Supplement_theorem_10
-- name    : PolyEulerFlow.Supplement.theorem_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:08:55.341276+00:00
-- url     : https://prove2.me/theorems/f890ae99-512d-4470-9664-f5588b149fc0
-- title:
--   Theorem 10 — a fixed-field robust prediction problem is PSPACE-complete
-- statement:
--   There exist a rational polynomial field $F(h,Z)$ on $\mathbb R^n$, a rational polynomial initialization $c(x,h)$, an integer $r>0$, a nonempty compact rational box $[lo,hi]$ and an output coordinate $o$ for which the following promise problem is PSPACE-complete under polynomial-time many-one reductions.
--
--   An instance is a binary integer $x$, a **unary** scale exponent $s\ge\ell(x)+4$ and a positive **binary** horizon $N$. It is promised that all unit-step executions
--   $$z_0=c(x,2^{-s}),\qquad z_{k+1}=z_k+F(2^{-s},z_k)+\xi_k,\qquad\|\xi_k\|_\infty\le2^{-rs},$$
--   stay in the box and, at every index $k\ge N$, all give an output $z_k(o)$ within $1/4$ of the same Boolean value. Decide that value.
--
--   Moreover, the hard instances can be chosen so that their decision is also stable after physical time $N$ for every admissible variable Euler mesh and for the continuous system with any measurable forcing of norm at most $2^{-rs}$: for every PSPACE language $L\subseteq\{0,1\}^*$ there is a polynomial-time reduction $w\mapsto(x,s,N)$ landing on instances that satisfy the promise with value $[w\in L]$ and also the strong promise (variable meshes and forced solutions, with solutions existing).
--
--   The field is fixed once and for all; only the encoded initial state, the precision and the observation horizon vary, so robustness and compactness do not make prediction tractable.
--
--   **Formalization Note** The promise and its strong form are `RobustPromiseValue` and `StrongPromiseValue`; completeness is `PromisePSPACEComplete` on the encoding $x$ binary, $s$ unary, $N$ binary.
--
--   Differences from the source:
--   - encoding: PSPACE-complete promise problem under polynomial-time many-one reductions → PromiseInPSPACE (one total polynomial-space machine on all instance encodings, correct on promised instances) and PromisePSPACEHard (every PSPACE language over {0,1} maps in polynomial time into promised instances with value [w ∈ L]); reason: the standard notion, with the published Mathlib multi-stack machine model
--   - encoding: x binary, s unary, N binary → self-delimiting binary words of x and N and the unary word of s, concatenated; reason: a fixed linear-length encoding with exactly the paper's unary/binary choices
--   - encoding: a compact rational box → [lo, hi] with rational corners and lo ≤ hi; reason: a nonempty compact rational box; an empty box admits no promised instance
--   - reading: the hard instances can be chosen so that their decision is also stable after physical time N for every admissible variable Euler mesh and for the continuous system with any measurable forcing of norm at most 2^{-rs} → a second hardness clause: reductions landing on instances satisfying StrongPromiseValue (variable meshes with drift ≤ 2^{-rs} correct at physical time ≥ N; forced solutions exist and all are correct for t ≥ N); reason: 'can be chosen' asserts the existence of such reductions; the disturbance bound on variable meshes is the same 2^{-rs}, the stronger reading
-- source:
--   Bournez, One Polynomial Field for Every Euler Step and the Flow: Polynomial Dynamics for P and PSPACE (manuscript, STOC 2027 submission, sha256 c4e01b2beb237b48b48e97294deb3c15dae11d39c5f136914567c5ca2ae1b119), Theorem 10, p.8 (PDF 10); restated with proof pp.44–45 (PDF 46–47)

import Mathlib
import Definitions.Def_PolyEulerFlow_Supplement_PromiseInPSPACE
import Definitions.Def_PolyEulerFlow_Supplement_RobustPromiseValue

namespace PolyEulerFlow.Supplement

open PolyEulerFlow

/-- **Theorem 10 (A fixed-field robust prediction problem)**, p.8 (PDF 10; restated p.44, PDF 46). Bournez, One Polynomial Field for Every
Euler Step and the Flow (manuscript, sha256 c4e01b2b…): "There exist a fixed rational polynomial field F(h, Z), a fixed rational polynomial
initialization c(x, h), an integer r > 0, a compact rational box and an output coordinate for which the following promise problem is
PSPACE-complete under polynomial-time many-one reductions. An instance consists of a binary integer x, a unary scale exponent s ≥ ℓ(x) + 4,
and a positive binary horizon N. It is promised that all unit-step executions from c(x, 2^{−s}), under active disturbances of norm at most
2^{−rs}, stay in the box and, at every index at least N, all give an output within 1/4 of the same Boolean value. Decide that value. The hard
instances can be chosen so that their decision is also stable after physical time N for every admissible variable Euler mesh and for the
continuous system with any measurable forcing of norm at most 2^{−rs}."

**Formalization Note.** Instances `(x, s, N)` are encoded by `encodePredInstance` (`x`, `N` binary, `s` unary). The promise with value `b`
is `RobustPromiseValue`; the last sentence is a second hardness clause whose reductions land in `StrongPromiseValue`. -/
theorem theorem_10 :
    ∃ (n : ℕ) (F : Fin n → MvPolynomial (Option (Fin n)) ℚ) (c : Fin n → MvPolynomial (Fin 2) ℚ) (r : ℕ)
      (lo hi : Fin n → ℚ) (o : Fin n),
      0 < r ∧ lo ≤ hi ∧
      PromisePSPACEComplete encodePredInstance (RobustPromiseValue F c r lo hi o) ∧
      ∀ L : Language Bool, OptimalQueuingComplexity.Restless.InPSPACE (id : List Bool → List Bool) (fun w => w ∈ L) →
        ∃ f : List Bool → ℕ × ℕ × ℕ,
          Nonempty (Turing.TM2ComputableInPolyTime (id : List Bool → List Bool) encodePredInstance f) ∧
          ∀ w, StrongPromiseValue F c r lo hi o (f w) (open Classical in decide (w ∈ L)) := by sorry

end PolyEulerFlow.Supplement
