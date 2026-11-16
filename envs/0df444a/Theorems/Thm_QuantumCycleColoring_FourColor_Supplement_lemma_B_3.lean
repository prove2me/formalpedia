-- Prove2me | Theorems.Thm_QuantumCycleColoring_FourColor_Supplement_lemma_B_3
-- name    : QuantumCycleColoring.FourColor.Supplement.lemma_B_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:32:49.357206+00:00
-- url     : https://prove2.me/theorems/d4dd41f7-fd07-44b4-981f-dfc8ff96c324
-- title:
--   Lemma B.3: $\Lambda$-mass $m\in[1/3,1/2]$ forces $\Lambda$-energy $\ge m^4(4m-1)^2/4$
-- statement:
--   Let $P$ be a PSD operator on $\mathbb C^N\otimes\mathbb C^N$ with $0\preceq P\preceq I$, and let $\Lambda\in\mathbb C^{N\times N}$ be PSD with $\|\Lambda\|_F=1$. Write $\mathcal E_\Lambda(P)=\mathrm{Tr}(\Lambda A\Lambda B)$ for the **$\Lambda$-energy**, with $A=\mathrm{Tr}_{\mathcal A}((\Lambda^2\otimes I)P)^\top$, $B=\mathrm{Tr}_{\mathcal B}((I\otimes\bar\Lambda^2)P)$; $\bar\Lambda$ is the entrywise conjugate. If
--   $$m:=\mathrm{Tr}\big(P(\Lambda^2\otimes\bar\Lambda^2)\big)\in\Big[\frac13,\frac12\Big],$$
--   then
--   $$\mathcal E_\Lambda(P)\ \ge\ \frac{m^4(4m-1)^2}{4}.$$
--
--   Unlike Lemma B.2, the bound stays positive at $m=1/3$, where it equals $1/2916$; this gives the three-colour constant of Theorem B.1.
--
--   Differences from the source:
--   - encoding: m = Tr(P(Λ²⊗Λ̄²)) and Λ-energy E_Λ(P) = Tr(ΛAΛB), complex traces that are real for PSD P, Λ → mass Λ P and energy Λ P are the real parts of these traces; reason: the traces are real for PSD P and Λ, so the values are the same
--   - encoding: ℂ^N with its standard basis, operators on ℂ^N ⊗ ℂ^N → vectors indexed by an arbitrary finite type d (N = card d), operators are matrices indexed by d × d with the Kronecker product for ⊗; reason: relabelling the standard basis; the same instances
--   - encoding: P PSD with 0 ⪯ P ⪯ I → P positive semidefinite and 1 − P positive semidefinite; reason: the definition of the Loewner order; the same instances
-- source:
--   Tom Gur, Longcheng Li, STOC 2027 submission #515 (October 2026), Lemma B.3, p.55 (proof pp.55–57)

import Mathlib
import Definitions.Def_QuantumCycleColoring_FourColor_MatrixAnalysis

open scoped Kronecker ComplexOrder

namespace QuantumCycleColoring.FourColor.Supplement

open QuantumCycleColoring.FourColor Matrix

/-- Lemma B.3, p.55 (Gur–Li, STOC 2027 #515). For PSD `P` on `ℂ^N ⊗ ℂ^N` with `0 ⪯ P ⪯ I` and
PSD `Λ` with `‖Λ‖_F = 1`, if `m := Tr(P(Λ² ⊗ Λ̄²)) ∈ [1/3, 1/2]` then
`E_Λ(P) ≥ m⁴(4m − 1)²/4`. -/
theorem lemma_B_3 {d : Type} [Fintype d] [DecidableEq d]
    (P : Matrix (d × d) (d × d) ℂ) (hP : P.PosSemidef) (hPI : (1 - P).PosSemidef)
    (Λ : Matrix d d ℂ) (hΛ : Λ.PosSemidef) (hΛF : frobNorm Λ = 1)
    (hm₁ : 1 / 3 ≤ mass Λ P) (hm₂ : mass Λ P ≤ 1 / 2) :
    mass Λ P ^ 4 * (4 * mass Λ P - 1) ^ 2 / 4 ≤ energy Λ P := by sorry

end QuantumCycleColoring.FourColor.Supplement
