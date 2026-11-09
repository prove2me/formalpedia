-- Prove2me | Theorems.Thm_PersistQMem_eq_67_68_kraus_density
-- name    : PersistQMem.eq_67_68_kraus_density
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:36:36.183784+00:00
-- url     : https://prove2.me/theorems/089cf7c8-4701-4e1b-b422-f44212701443
-- title:
--   §6.6, (67)–(68) — a measurable complete instrument has a measurable Kraus density
-- statement:
--   Let $\mathcal E$ be a complete completely positive instrument from $d\times d$ to $K\times K$ matrices ($d\ge1$) on a measurable record space, with Choi measure $\Gamma$. Then:
--
--   1. $\mu(S)=d^{-1}\operatorname{Tr}\Gamma(S)$ is a finite measure;
--   2. there is a measurable matrix field $J$ with
--   $$\Gamma(S)=\int_SJ(a)\,d\mu(a),\qquad J(a)\succeq0\ \text{ for }\mu\text{-almost every }a;\tag{67}$$
--   3. there are measurable Kraus operators $M_{a,l}$, $l\in\{1,\dots,Kd\}$, such that
--   $$\mathcal E_a(Z)=\sum_{l=1}^{Kd}M_{a,l}ZM_{a,l}^*,\qquad\int\sum_lM_{a,l}^*M_{a,l}\,d\mu(a)=I_d,\tag{68}$$
--   where $\mathcal E_a$ is the density of $\mathcal E$ with respect to $\mu$: $\mathcal E(S)(Z)=\int_S\mathcal E_a(Z)\,d\mu(a)$.
--
--   This turns an instrument-valued measure into the Kraus-density form used by the measurable protocol model.
--
--   Differences from the source:
--   - encoding: E_a(Z) = Σ_l M_{a,l} Z M_{a,l}* (the density of E) → E(S)(Z) = ∫_S Σ_l M_{a,l} Z M_{a,l}* dμ for every measurable S and every Z; reason: this is what it means for E_a to be the density of E
--   - encoding: matrix-valued integrals; μ(S) = d⁻¹ Tr Γ(S) → entrywise Bochner integrals, each entry asserted integrable; μ S = ofReal(d⁻¹ Re Tr Γ(S)); reason: Lean convention; Tr Γ(S) is real and nonnegative
--   - encoding: Choi matrix Γ → choi E = Σ |i⟩⟨j| ⊗ E(|i⟩⟨j|) on C^d ⊗ C^K (input ⊗ output); reason: the order used by (72)–(73)
-- source:
--   Tao, Shen, Structural Lower Bounds for Quantum Property Estimation with Persistent Memory, STOC 2027 submission (manuscript of 2026-11-03, sha256 6d48ad24…), §6.6, (67)–(68), p.27 (PDF p.30)

import Mathlib
import Definitions.Def_PersistQMem_CPInstrumentMeasure

open scoped Matrix ComplexOrder
open MeasureTheory

namespace PersistQMem

/-- **§6.6, (67)–(68), p.27: one measurable complete instrument has a Kraus density** (Tao, Shen,
*Structural Lower Bounds for Quantum Property Estimation with Persistent Memory*, STOC 2027
submission, manuscript of 2026-11-03, sha256 6d48ad24…, §6.6, (67)–(68), p.27). Let `E` be a
complete CP instrument from `d × d` to `K × K` matrices (`d ≥ 1`) on a measurable record space, with
Choi measure `Γ`. Then
1. `μ(S) = d⁻¹ Tr Γ(S)` is a finite measure;
2. (67) there is a measurable matrix field `J` with `J(a) ⪰ 0` for `μ`-almost every `a` and
   `Γ(S) = ∫_S J dμ` for every measurable `S`;
3. (68) there are measurable Kraus fields `M_{a,l}`, `l ∈ {1, …, Kd}`, with
   `E(S)(Z) = ∫_S Σ_l M_{a,l} Z M_{a,l}* dμ(a)` for every measurable `S` and every `Z` (that is,
   `E_a(Z) = Σ_l M_{a,l} Z M_{a,l}*` is the density of `E` with respect to `μ`) and
   `∫ Σ_l M_{a,l}* M_{a,l} dμ(a) = I_d`.

**Formalization Note.** Matrix integrals are entrywise Bochner integrals; every entry is asserted
integrable. -/
theorem eq_67_68_kraus_density {X : Type} [MeasurableSpace X] {d K : ℕ} (hd : 1 ≤ d)
    (E : CPInstrumentMeasure X d K) :
    ∃ μ : Measure X, IsFiniteMeasure μ ∧
      (∀ S, MeasurableSet S → μ S = ENNReal.ofReal ((d : ℝ)⁻¹ * (choi (E.E S)).trace.re)) ∧
    (∃ J : X → Matrix (Fin d × Fin K) (Fin d × Fin K) ℂ,
      (∀ q q', Measurable fun a => J a q q') ∧ (∀ᵐ a ∂μ, (J a).PosSemidef) ∧
      ∀ S, MeasurableSet S → ∀ q q', IntegrableOn (fun a => J a q q') S μ ∧
        choi (E.E S) q q' = ∫ a in S, J a q q' ∂μ) ∧
    ∃ Mk : X → Fin (K * d) → Matrix (Fin K) (Fin d) ℂ,
      (∀ l o c, Measurable fun a => Mk a l o c) ∧
      (∀ S, MeasurableSet S → ∀ (Z : Matrix (Fin d) (Fin d) ℂ) (o o' : Fin K),
        IntegrableOn (fun a => (∑ l, Mk a l * Z * (Mk a l)ᴴ) o o') S μ ∧
        E.E S Z o o' = ∫ a in S, (∑ l, Mk a l * Z * (Mk a l)ᴴ) o o' ∂μ) ∧
      ∀ c c' : Fin d, Integrable (fun a => (∑ l, (Mk a l)ᴴ * Mk a l) c c') μ ∧
        ∫ a, (∑ l, (Mk a l)ᴴ * Mk a l) c c' ∂μ = (1 : Matrix (Fin d) (Fin d) ℂ) c c' := by sorry

end PersistQMem
