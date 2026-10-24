-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P42_concentration
-- name    : QAlgorithms.Papers.Independent.Support50.P42.concentration
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T22:11:33.193024+00:00
-- url     : https://prove2.me/theorems/98cb8cfc-3bdd-4faf-b281-6b9fc8df4672
-- title:
--   Entropy-efficient exact singlet concentration
-- statement:
--   Let $\psi$ be a normalized pure state of two positive finite-dimensional systems shared by Alice and Bob. Let $E=S(\rho_B)$ be its entropy of entanglement in bits. Local operations and classical communication admit protocols on every number $n$ of identical copies whose outputs are exact integer numbers of standard singlets. If $Y_n$ is their expected singlet count, then there are constants $C>0$ and $N$, depending only on the fixed input state, such that
--
--   $$nE-C\log_2(n+1)\le Y_n\le nE\quad(n\ge N),\qquad \lim_{n\to\infty}\frac{Y_n}{n}=E.$$
--
--   If $E=0$, all these yields are zero. The expected singlet count refers to actual local protocol leaves after standardization, rather than to a fractional logarithm of a Schmidt rank. This is the paper's asymptotic conservation of pure-state entanglement.
-- source:
--   Concentrating Partial Entanglement by Local Operations, arXiv:quant-ph/9511030v1, PDF p. 1, Abstract, §I: asymptotically efficient concentration of pure entanglement

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P42

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P42

open scoped BigOperators Matrix ComplexConjugate

open MeasureTheory ProbabilityTheory

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the exact accepted objects, without introducing same-name aliases.

open Information100.P21 (Op Vec FiniteLOCC)

open Dependency50.P42 (dimensionedPower singlets)

open Dependency50.P48 (pureFidelity)

open Gap48.P32 (pairOfState)

open Next46.P39 (rectAct)

/-- Abstract; PDF pp.4--9,15: exact singlet yield in expectation, for general
finite-dimensional pure inputs. Constants depend on the fixed input and precede
n. The log-rank yield and standardization loss are not identified with each other. -/
theorem concentration (s : Shared) (hpure : IsPureShared s) :
    ∃ Y : ℕ → ℝ, (∀ n, ExactYield s n (Y n)) ∧
      (∃ C : ℝ, 0<C ∧ ∃ N : ℕ, ∀ n≥N,
        (n : ℝ)*ent s-C*Real.logb 2 (n+1 : ℕ)≤Y n ∧ Y n≤(n : ℝ)*ent s) ∧
      Filter.Tendsto (fun n : ℕ => Y n/(n : ℝ)) Filter.atTop (nhds (ent s)) ∧
      (ent s=0 → ∀ n, Y n=0) := by sorry

end QAlgorithms.Papers.Independent.Support50.P42

end
