-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P28_no_attainment_and_sufficiency
-- name    : QAlgorithms.Papers.Independent.Dependency50.P28.no_attainment_and_sufficiency
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:11:03.925838+00:00
-- url     : https://prove2.me/theorems/95448325-e7ed-4728-8547-fbd6736fb6c9
-- title:
--   Exact measurement attainment is incompatible with sufficiency
-- statement:
--   Let D be a family of functions on pairs of density operators over all finite dimensions. Exact single-shot measurement attainment (AM) requires an attaining finite measurement for each pair. Sufficiency (S) requires that equality under any CPTP map imply a CPTP map recovering both states. Then
--
--   Write $Q_\alpha(\rho\Vert\sigma)=\operatorname{Tr}(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)})^\alpha$ and $F_\alpha=\log Q_\alpha$. Powers are evaluated only on positive eigenvalues and are zero on the kernel, even at exponent zero; scalar logarithms satisfy $\log0=-\infty$.
--
--   The normalized new divergence is $\widetilde D_\alpha=(F_\alpha-\log\operatorname{Tr}\rho)/(\alpha-1)$ when the supports are nested or $0<\alpha<1$, and is $+\infty$ otherwise; the first argument has positive trace. For states the trace-normalizing term is zero.
--
--   Here $D(\rho\Vert\sigma)=\operatorname{Tr}[\rho(\log\rho-\log\sigma)]/\operatorname{Tr}\rho$ on nested supports and $+\infty$ otherwise, and $D_{\max}(\rho\Vert\sigma)=\inf\{a\in\mathbb R:\rho\leq e^a\sigma\}$, with the empty infimum equal to $+\infty$. All operator inequalities are in Loewner order.
--
--   $D_{\max}$ is also the infinite-order new divergence, and $\widetilde D_{1/2}=-2\log F$ for the unsquared Uhlmann root fidelity $F$. Exact attainment refers to a finite measurement, with arbitrary outcome cardinality.
--
--   $$
--   \neg(\mathrm{AM}(D)\wedge\mathrm{S}(D)),\qquad\neg\mathrm{S}(\widetilde D_{1/2}),\qquad\neg\mathrm{S}(D_{\max}).
--   $$
--
--   This separates exact measurement attainment from recoverability-based sufficiency.
-- source:
--   Quantum hypothesis testing and the operational interpretation of the quantum Renyi relative entropies, arXiv:1309.3228v5, PDF p. 25, Corollary A.9 No quantum divergence can satisfy (A)+(S). In particular, D1/2                 and D∞       do not

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P28

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P28

open scoped Matrix ComplexConjugate ComplexOrder BigOperators

open Filter QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P07 (support positivePart positiveProjection)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- arXiv:1309.3228v5, PDF p.25: Exact measurement attainment is incompatible with sufficiency. Printed (A) means AM, as defined on p.23 and used in the proof. The corollary is on PDF p.25, not p.24. Quantification across dimensions avoids the singleton-space vacuity. -/
theorem no_attainment_and_sufficiency (d : Divergence) :
    ¬ (AM d ∧ Sufficiency d) ∧
    ¬ Sufficiency (newFamily (1 / 2)) ∧ ¬ Sufficiency maxFamily := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P28

end
