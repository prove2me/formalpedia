-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P38_corollary12
-- name    : QAlgorithms.Papers.Independent.Support50.P38.corollary12
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T22:02:33.686984+00:00
-- url     : https://prove2.me/theorems/40af2cdf-5937-4bc9-9a0a-d656e7ca9654
-- title:
--   Asymptotic channel simulation and feedback rate region
-- statement:
--   Let $W$ be a channel between finite nonempty alphabets $X,Y$. All rates are in bits per use. For $0\le\lambda<1$ and $R,C\ge0$, say that $(R,C)$ is achievable at asymptotic error $\lambda$ if for every error slack $\eta>0$ and rate slack $\epsilon>0$, every sufficiently large positive $n$ admits a shared-seed code with deterministic output from seed and message, communication at most $n(R+\epsilon)$, prepared randomness at most $n(C+\epsilon)$, and total variation at most $\lambda+\eta$ for every input word. Then
--
--   $$
--   (R,C)\text{ is achievable}\iff
--   R\ge\max_P I(P;W)\quad\text{and}\quad R+C\ge\max_P H(PW).
--   $$
--   The two maxima range independently over all input probability laws and need not have a common maximizer. Independent local randomness is free. This characterizes channel simulation with noiseless passive feedback, including boundary rates by arbitrary slack.
-- source:
--   Compression of sources of probability distributions and density operators, arXiv:quant-ph/0208131v1, PDF p. 6, Corollary 12

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P38

open scoped BigOperators Matrix ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Frontier30.P12 (IsStochastic)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon labelInformation)

attribute [local instance] Classical.propDecidable

/-- Corollary 12, PDF p.6: exact asymptotic rate region for uniform-on-input channel
simulation with noiseless passive feedback. The two suprema may use different input laws;
expressing each constraint for every law avoids any assumption of a common maximizer. -/
theorem corollary12 {A B : Type} [Fintype A] [Fintype B] [DecidableEq B]
    [Nonempty A] [Nonempty B] (w : A → B → ℝ) (hw : IsStochastic w)
    (error communication randomness : ℝ) (he : 0 ≤ error) (he1 : error < 1)
    (hr : 0 ≤ communication) (hc : 0 ≤ randomness) :
    FeedbackRates w error communication randomness ↔
      ((∀ p : A → ℝ, IsLaw p → sourceInformationBits p w ≤ communication) ∧
       (∀ p : A → ℝ, IsLaw p → shannon (sourceOutputMarginal p w) ≤ communication + randomness)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P38

end
