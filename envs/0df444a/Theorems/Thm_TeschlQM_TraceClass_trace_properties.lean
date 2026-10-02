-- Prove2me | Theorems.Thm_TeschlQM_TraceClass_trace_properties
-- name    : TeschlQM.TraceClass.trace_properties
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T10:05:38.468688+00:00
-- url     : https://prove2.me/theorems/bc4fa0c8-3729-4ee1-bd80-5aad2c8d857c
-- title:
--   Lemma 6.16 — Elementary properties of the trace
-- statement:
--   Let $\mathfrak{H}$ be a complex Hilbert space, let $K, K_1, K_2$ be trace class and let $A \in \mathfrak{L}(\mathfrak{H})$ be bounded. Then:
--
--   1. the trace is linear: $\operatorname{tr}(K_1 + K_2) = \operatorname{tr}(K_1) + \operatorname{tr}(K_2)$ and $\operatorname{tr}(cK) = c\operatorname{tr}(K)$ for $c \in \mathbb{C}$;
--   2. $\operatorname{tr}(K^*) = \overline{\operatorname{tr}(K)}$;
--   3. if $K_1 \le K_2$, then $\operatorname{tr}(K_1) \le \operatorname{tr}(K_2)$;
--   4. $\operatorname{tr}(AK) = \operatorname{tr}(KA)$.
--
--   **Formalization Note.** $K_1 \le K_2$ is Mathlib's Loewner order on `H →L[ℂ] H`: $K_2 - K_1$ is a positive operator, i.e. $\langle \varphi, K_1\varphi\rangle \le \langle\varphi, K_2\varphi\rangle$ for all $\varphi$. The conclusion uses the partial order on $\mathbb{C}$ (`ComplexOrder`): $\operatorname{tr}(K_2) - \operatorname{tr}(K_1)$ is a nonnegative real number. The trace is the one of Lemma 6.15, computed in a fixed orthonormal basis.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 144, Lemma 6.16

import Mathlib
import Definitions.Def_TeschlQM_TraceClass_schattenClass
import Definitions.Def_TeschlQM_TraceClass_trace

namespace TeschlQM.TraceClass

open scoped ComplexOrder

/-- Teschl, Lemma 6.16, p. 144. Suppose `K`, `K₁`, `K₂` are trace class and `A` is bounded.
(i) The trace is linear: `tr(K₁ + K₂) = tr(K₁) + tr(K₂)` and `tr(cK) = c tr(K)`.
(ii) `tr(K*) = tr(K)*` (complex conjugate).
(iii) If `K₁ ≤ K₂` (i.e. `K₂ - K₁ ≥ 0`, Mathlib's Loewner order), then `tr(K₁) ≤ tr(K₂)`, in the
partial order of `ℂ` (`tr(K₂) - tr(K₁)` is a nonnegative real number).
(iv) `tr(AK) = tr(KA)`. -/
theorem trace_properties {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (K K₁ K₂ A : H →L[ℂ] H) (hK : IsTraceClass K) (hK₁ : IsTraceClass K₁)
    (hK₂ : IsTraceClass K₂) :
    (trace (K₁ + K₂) = trace K₁ + trace K₂ ∧ ∀ c : ℂ, trace (c • K) = c * trace K) ∧
    trace (ContinuousLinearMap.adjoint K) = starRingEnd ℂ (trace K) ∧
    (K₁ ≤ K₂ → trace K₁ ≤ trace K₂) ∧
    trace (A * K) = trace (K * A) := by sorry

end TeschlQM.TraceClass
