-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P69_diamondStability
-- name    : QAlgorithms.Papers.Independent.Information100.P69.diamondStability
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:01:25.262749+00:00
-- url     : https://prove2.me/theorems/821159ea-9ef8-4f65-b05c-66988eace9f2
-- title:
--   Diamond-norm stability
-- statement:
--   Assume F1–F3 and let $T_n:A^{\otimes n}\to B^{\otimes n}$ be arbitrary CPTP maps with $\|T_n-\mathcal N^{\otimes n}\|_\diamond\to0$. Define $\widehat\beta_{\varepsilon,n}$ by the same composite parallel testing optimization, replacing the target by $T_n$ and keeping $\mathcal F_n$. For each fixed $0<\varepsilon<1$,
--   $$\lim_{n\to\infty}-\frac1n\log_2\widehat\beta_{\varepsilon,n}=R_{\mathcal F}(\mathcal N).$$
--   The perturbed targets may be correlated across uses. This is stability of the testing rate; it makes no additional entropy-continuity assertion.
--
--   The testing model uses one normalized pure input, possibly entangled across uses and with a reference, and one acceptance effect shared by every alternative. The symbol $\le_{\rm CP}$ means that the difference of the larger and smaller maps is completely positive; $\|\cdot\|_\diamond$ is the full diamond norm. Information quantities use base-2 logarithms.
-- source:
--   A Generalized Stein Lemma for Quantum Channels, arXiv:2609.30762v1, PDF p. 18, Corollary 13

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P69

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Information100.P69

attribute [local instance] Classical.propDecidable Classical.decEq

section Statements

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- Corollary 13, arbitrary correlated CPTP target perturbations, PDF pp.18–19. -/
theorem diamondStability [Nonempty A] [Nonempty B] (N : Superop A B) (hN : IsChannel N) (F : BlockFamily A B)
    (omega : Matrix B B ℂ) (hF : Admissible F omega)
    (T : (n : ℕ) → Superop (Sites A n) (Sites B n)) (hT : ∀ n, 1 ≤ n → IsChannel (T n))
    (herr : Tendsto (fun j : ℕ => diamond (T (j+1)-power N (j+1))) atTop (nhds 0))
    (eps : ℝ) (heps : 0 < eps) (heps1 : eps < 1) :
    Tendsto (fun j : ℕ => exponent (T (j+1)) (F (j+1)) eps/(j+1)) atTop (nhds (rate N F)) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Information100.P69

end
