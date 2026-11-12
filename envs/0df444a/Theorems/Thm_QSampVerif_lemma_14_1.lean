-- Prove2me | Theorems.Thm_QSampVerif_lemma_14_1
-- name    : QSampVerif.lemma_14_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:35:38.782198+00:00
-- url     : https://prove2.me/theorems/8fa52982-be9a-431d-a19b-8080835eb555
-- title:
--   Lemma 14.1 — resampling accepted outputs: $\mathcal T(\delta_\bot)=\delta_\bot$, $\mathcal T(|y\rangle\langle y|)=P_C$, $\mathcal T(\rho)=pP_C+(1-p)\delta_\bot$
-- statement:
--   For every well-formed target circuit $C$ with $m$ output wires there is a resampling circuit $R_C$ on the alphabet $\mathcal Y\cup\{\bot\}$, $\mathcal Y=\{0,1\}^m$, whose description is computed from $\langle C\rangle$ by one classical polynomial-time map, such that its induced map $\mathcal T$ on diagonal operators satisfies
--
--   1. $\mathcal T(\delta_\bot)=\delta_\bot$;
--   2. $\mathcal T(|y\rangle\langle y|)=P_C$ for every $y\in\mathcal Y$;
--   3. for every output distribution $\rho$, with $p=\mathrm{Tr}(\rho_{\mathrm{acc}})=\sum_{y\in\mathcal Y}\rho(y)$,
--   $$\mathcal T(\rho)=p\,P_C+(1-p)\,\delta_\bot;$$
--   4. for every diagonal Hermitian $Y$, with $Y_{\mathrm{acc}}$ its part on $\mathcal Y$, $\mathcal T(Y_{\mathrm{acc}})=\mathrm{Tr}(Y_{\mathrm{acc}})\,P_C$, including when $Y$ has negative entries.
--
--   Here $P_C$ gives $\bot$ probability zero. The lemma turns the real output into the ideal experiment while preserving the actual acceptance probability; it is the comparison step of the soundness proof (Theorem 14.2).
--
--   Differences from the source:
--   - encoding: diagonal operators / output distributions on 𝒴 ∪ {⊥}, and the channel's action on them → real functions on Option (Qubits m) and the stochastic map induced by a circuit's Born-rule transition probabilities; reason: the output register is classical; same objects
--   - reading: Ĉ (the compiled H/CCZ circuit with output distribution P_C) and "time polynomial in the size of Ĉ" → the target circuit C itself; the resampling circuit's description is computed from ⟨C⟩ by a PolyTimeComputable map; reason: in the pinned-down model C is already over a finite gate set (paper.md decision 3) and Ĉ enters only through P_C; uniform polynomial-time generation is the stronger reading of "implementable in time polynomial"
-- source:
--   Chung, Cojocaru, Lee, Lin, Classical Verification of Quantum Sampling with Negligible Error, STOC 2027 submission (held version, sha256 dbc19d8f…7ee7), Lemma 14.1, (481), p.184 (PDF 185)

import Definitions.Def_QSampVerif_Resampler

set_option autoImplicit false

namespace QSampVerif

open QAlgorithms QAlgorithms.Complexity

/-- Chung, Cojocaru, Lee, Lin, STOC 2027 submission (held version, sha256 dbc19d8f…7ee7),
Lemma 14.1 (Resampling accepted outputs), (481), p.184 (PDF 185).

There is a resampling circuit `R_C` for every target circuit `C`, produced from the description
of `C` by a classical polynomial-time map, whose induced map `T` on diagonal operators of the
output register `Y ∪ {⊥}` (`Y = {0,1}^{|outW|}`) satisfies `T(δ_⊥) = δ_⊥`, `T(|y⟩⟨y|) = P_C` for
`y ∈ Y`, `T(ρ) = p P_C + (1 − p) δ_⊥` with `p = Tr(ρ_acc)` for every output distribution `ρ`, and
`T(Y_acc) = Tr(Y_acc) P_C` for every diagonal Hermitian `Y`. -/
theorem lemma_14_1 :
    ∃ (R : (C : TargetCircuit) → Resampler C.outW.length) (f : Str → Str),
      PolyTimeComputable f ∧
      ∀ C : TargetCircuit, C.Valid →
        f C.encode = (R C).encode ∧ (R C).Valid ∧
        (R C).apply deltaNone = deltaNone ∧
        (∀ y : Qubits C.outW.length,
          (R C).apply (fun z => if z = some y then 1 else 0) = C.pushSomeQ) ∧
        (∀ ρ : Option (Qubits C.outW.length) → ℝ, (∀ z, 0 ≤ ρ z) → ∑ z, ρ z = 1 →
          (R C).apply ρ = fun z =>
            (∑ y, ρ (some y)) * C.pushSomeQ z + (1 - ∑ y, ρ (some y)) * deltaNone z) ∧
        (∀ Y : Option (Qubits C.outW.length) → ℝ,
          (R C).apply (fun z => if z = none then 0 else Y z) =
            fun z => (∑ y, Y (some y)) * C.pushSomeQ z) := by sorry

end QSampVerif
