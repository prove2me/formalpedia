-- Prove2me | Theorems.Thm_PrivOptTest_lemma_2_2
-- name    : PrivOptTest.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:58:10.868026+00:00
-- url     : https://prove2.me/theorems/98505a4d-a705-445f-b2e5-08d546164c7c
-- title:
--   Lemma 2.2, p.14 — differential privacy bounds internal information cost
-- statement:
--   Let $\mathcal A,\mathcal B$ be finite, $E_A:\mathcal A\to\mathcal X^n$, $E_B:\mathcal B\to\mathcal X^n$ encodings with diameters $\Delta_A=\max_{a,a'}d_{\mathrm{ham}}(E_A(a),E_A(a'))$ and $\Delta_B$, and $(A,B)\sim\mu$. If $\Pi$ is a well-formed $\varepsilon$-differentially private two-party protocol, $\varepsilon>0$, and $T$ is the public transcript of $\Pi$ on $(E_A(A),E_B(B))$ (public randomness, messages, output), then, in bits,
--   $$I(A;T\mid B)+I(B;T\mid A)\le\frac{\varepsilon(\Delta_A+\Delta_B)}{\ln2}.$$
--
--   This connects privacy to information complexity, the engine of the lower bound.
--
--   Differences from the source:
--   - encoding: I(A;T|B) + I(B;T|A) → infoCost: averages of KL divergences to the conditional mixtures, divided by ln 2; reason: the standard expression of conditional mutual information for finite A, B
--   - encoding: "an ε-differentially private protocol" → IsWellFormed and IsPrivate ε with ε > 0; reason: Definition 2.1 with the protocol conventions of Definition 1.2
-- source:
--   M. Haghifam, K. K. Patel, A. Blum, G. Fanti, J. Ziani, Should We Combine Our Data? Algorithms and Limits for Privately Assessing Data Sharing, arXiv:2611.03599 (manuscript sha256 4ac94dcf…), Lemma 2.2, p.14; Definition 2.1, pp.13–14

import Mathlib
import Definitions.Def_PrivOptTest_Protocol
import Definitions.Def_PrivOptTest_infoCost

open MeasureTheory

namespace PrivOptTest

/-- **Lemma 2.2** (p.14). Let `A`, `B` be finite, let `E_A : A → 𝒳ⁿ`, `E_B : B → 𝒳ⁿ` encode inputs as
datasets, with encoding diameters `Δ_A = max d_ham(E_A(a), E_A(a′))`, `Δ_B` likewise. If `(A, B) ∼ μ` and
Alice and Bob run an ε-differentially private protocol on `(E_A(A), E_B(B))`, the public transcript `T`
(public randomness, all messages, output) has internal information cost, in bits,
`I(A; T | B) + I(B; T | A) ≤ ε(Δ_A + Δ_B)/ln 2`.
Source: Haghifam, Patel, Blum, Fanti, Ziani, *Should We Combine Our Data?*, arXiv:2611.03599 (manuscript sha256 4ac94dcf…), Lemma 2.2, p.14; Definition 2.1, pp.13–14.

**Formalization Note.** The information cost is `infoCost` (conditional mutual informations as averages
of Kullback–Leibler divergences, for finite `A`, `B`). The protocol is well-formed (measurable,
probability coins, terminating) and private in the sense of Definition 2.1 on all inputs. -/
theorem lemma_2_2 {A B D Out : Type} [Fintype A] [Fintype B] [DecidableEq D] [MeasurableSpace Out]
    {n : ℕ} (EA : A → Fin n → D) (EB : B → Fin n → D) (μ : PMF (A × B))
    (Pr : Protocol (Fin n → D) Out) (ε : ℝ) (hε : 0 < ε) (hwf : Pr.IsWellFormed)
    (hpriv : Pr.IsPrivate ε) :
    infoCost μ (fun a b => Pr.transcriptLaw (EA a) (EB b)) ≤
      ENNReal.ofReal (ε * ((encDiam EA : ℝ) + encDiam EB) / Real.log 2) := by sorry

end PrivOptTest
