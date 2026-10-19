-- Prove2me | Theorems.Thm_PuhaWardFluid_Limit_lemma_8
-- name    : PuhaWardFluid.Limit.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:22:34.289982+00:00
-- url     : https://prove2.me/theorems/e4205ccb-eb2d-4c32-b510-a0217e53da12
-- title:
--   Lemma 8, p. 22, with (K.2) read as relative compactness — the fluid-scaled real processes are relatively compact in D(ℝ₊), C-tight under Assumption 5
-- statement:
--   Consider a sequence of admissible HL control policies, one for each $N$, and suppose that Assumptions 1, 2 and 3 hold, with Assumption 2 read as below. Then for each class $j$, $f_j\in C^1_c([0,H^s_j))$, $\varsigma_j\in C^1_c([0,H^r_j))$, $\varphi_j\in C_b([0,H^s_j)\times\mathbb R_+)$ and $\psi_j\in C_b([0,H^r_j)\times\mathbb R_+)$, each of the sequences
--   $$\{\bar E^N_j\},\ \{\bar X^N_j\},\ \{\langle f_j,\bar\nu^N_j\rangle\},\ \{\langle\varsigma_j,\bar\eta^N_j\rangle\},\ \{\langle1,\bar\eta^N_j\rangle\},\ \{\bar B^N_j\},\ \{\bar Q^N_j\},\ \{\bar R^N_j\},\ \{\bar D^N_j\},\ \{\bar K^N_j\},$$
--   $$\{\bar{\mathcal D}^N_j(\varphi_j,\cdot)\},\ \{\bar{\mathcal A}^N_{s,j}(\varphi_j,\cdot)\},\ \{\bar{\mathcal S}^N_j(\psi_j,\cdot)\},\ \{\bar{\mathcal A}^N_{r,j}(\psi_j,\cdot)\},\ \{\bar I^N\},\ \{\bar D^N_\Sigma\}$$
--   (indexed by $N\in\mathbb N$) is relatively compact in $\mathbf D(\mathbb R_+)$, hence tight. If Assumption 5 also holds, each of them is C-tight.
--
--   Here a bar denotes division by $N$. This lemma, with its measure-valued analogue Lemma 9, gives the tightness Theorem 2 on which the proof of Theorem 1 rests.
--
--   **Formalization Note** As printed, (K.2) of Kurtz' criteria asks only that $\lim_{\varepsilon\to0}\sup_N\mathbb E|H^N(t+\varepsilon)-H^N(t)|^q=0$ at rational $t$, which does not imply relative compactness in $\mathbf D$ (two unit jumps $1/N$ apart at a uniform time satisfy it). The first branch of Assumption 2 is therefore read as "$\{\bar K^N_j\}_N$ is relatively compact in $\mathbf D(\mathbb R_+)$ for each $j$"; the second branch, inequality (55), is as printed. Under Assumption 5.3, the only way Theorem 1 uses this lemma, this reading holds. The C-tightness part assumes Assumption 5 as printed in addition.
-- source:
--   Puha & Ward, Fluid limits for multiclass many-server queues with general reneging distributions and head-of-the-line scheduling, Math. Oper. Res., Articles in Advance (21 Dec 2021), doi:10.1287/moor.2021.1166, p. 22 (PDF 23), Lemma 8 (Assumption 2 p. 17, (K.2) p. 34)

import Mathlib
import Definitions.Def_PuhaWardFluid_Limit_Queue

open MeasureTheory
open scoped NNReal ENNReal

namespace PuhaWardFluid.Limit

/-- **Lemma 8** (p. 22), with Assumption 2's (K.2) branch read as relative compactness of
`{K̄^N_j}_N`. Under Assumptions 1, 2 and 3, for each class `j`, `f_j ∈ C¹_c([0, H^s_j))`,
`ς_j ∈ C¹_c([0, H^r_j))`, `φ_j ∈ C_b([0, H^s_j) × ℝ₊)` and `ψ_j ∈ C_b([0, H^r_j) × ℝ₊)`, the
sequences `{Ē^N_j}`, `{X̄^N_j}`, `{⟨f_j, ν̄^N_j⟩}`, `{⟨ς_j, η̄^N_j⟩}`, `{⟨1, η̄^N_j⟩}`, `{B̄^N_j}`,
`{Q̄^N_j}`, `{R̄^N_j}`, `{D̄^N_j}`, `{K̄^N_j}`, `{𝒟̄^N_j(φ_j, ·)}`, `{𝒜̄^N_{s,j}(φ_j, ·)}`,
`{𝒮̄^N_j(ψ_j, ·)}`, `{𝒜̄^N_{r,j}(ψ_j, ·)}`, `{Ī^N}` and `{D̄^N_Σ}` are relatively compact in `D(ℝ₊)`;
if Assumption 5 also holds, each of them is C-tight. -/
theorem lemma_8 {J : ℕ} (L : ClassLaws J) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Q : QueueSeq J Ω) (hQ : ∀ N : ℕ+, Q.IsAdmissibleHL L P N)
    (E : Ω → ℝ≥0 → Fin J → ℝ) (Z0 : Ω → Xsp L)
    (hA1 : Assumption1 P Q E) (hA2 : Assumption2RC L P Q) (hA3 : Assumption3 L P Q Z0) :
    ∀ (j : Fin J) (f f' ς ς' : ℝ → ℝ) (φ ψ : ℝ → ℝ → ℝ),
      IsC1c (L.Hs j) f f' → IsC1c (L.Hr j) ς ς' →
      ContinuousOn (Function.uncurry φ) (markDom (L.Hs j)) →
      (∃ C : ℝ, ∀ p ∈ markDom (L.Hs j), |φ p.1 p.2| ≤ C) →
      ContinuousOn (Function.uncurry ψ) (markDom (L.Hr j)) →
      (∃ C : ℝ, ∀ p ∈ markDom (L.Hr j), |ψ p.1 p.2| ≤ C) →
      let seqs : List (ℕ → Ω → ℝ≥0 → ℝ) :=
        [fun n ω t => Q.Ebar n.succPNat ω t j,
         fun n ω t => Q.Xbar L n.succPNat ω t j,
         fun n ω t => pair f (Q.nubar L n.succPNat ω t j),
         fun n ω t => pair ς (Q.etabar L n.succPNat ω t j),
         fun n ω t => mass1 (Q.etabar L n.succPNat ω t j),
         fun n ω t => Q.B L n.succPNat ω t j / (n.succPNat : ℝ),
         fun n ω t => Q.Qlen L n.succPNat ω t j / (n.succPNat : ℝ),
         fun n ω t => (Q.R L n.succPNat ω t j : ℝ) / (n.succPNat : ℝ),
         fun n ω t => (Q.D L n.succPNat ω t j : ℝ) / (n.succPNat : ℝ),
         fun n ω t => Q.Kbar n.succPNat ω t j,
         fun n ω t => Q.Dmark L n.succPNat ω φ t j / (n.succPNat : ℝ),
         fun n ω t => Q.Acomp_s L n.succPNat ω φ t j / (n.succPNat : ℝ),
         fun n ω t => Q.Smark L n.succPNat ω ψ t j / (n.succPNat : ℝ),
         fun n ω t => Q.Acomp_r L n.succPNat ω ψ t j / (n.succPNat : ℝ),
         fun n ω t => Q.I L n.succPNat ω t / (n.succPNat : ℝ),
         fun n ω t => (Q.DSum L n.succPNat ω t : ℝ) / (n.succPNat : ℝ)]
      (∀ H ∈ seqs, RelCompactInDist dR P H) ∧
        (Assumption5 L P Q E Z0 → ∀ H ∈ seqs, CTight dR P H) := by sorry

end PuhaWardFluid.Limit
