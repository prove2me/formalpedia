-- Prove2me | Theorems.Thm_QStateSearch_measurable_maximizer
-- name    : QStateSearch.measurable_maximizer
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:21:17.962358+00:00
-- url     : https://prove2.me/theorems/c11f6480-7cc1-4b9b-a51f-b13320ff30e4
-- title:
--   Proof of Theorem 4 — continuity in $\psi$ and a measurable maximizing prover
-- statement:
--   Let $V$ be a classical-message verifier. Then
--
--   1. for every deterministic classical prover $P$, the acceptance probability $\psi\mapsto\mathrm{Acc}_{R_\psi}(V,P)$ is continuous on $\mathbb C^D$;
--   2. there is a measurable family $\psi\mapsto P_\psi$ of deterministic classical provers such that for every $\psi$
--   $$
--   \big|\mathrm{Acc}_{R_\psi}(V,P_\psi)-\mathrm{Acc}_I(V,P_\psi)\big|=\max_P\big|\mathrm{Acc}_{R_\psi}(V,P)-\mathrm{Acc}_I(V,P)\big| .
--   $$
--
--   The hybrid argument fixes one maximizing prover per hidden state and needs the choice to be measurable so that the compatible sets of Lemma 3 are Haar measurable.
--
--   **Formalization Note** "Measurable" means every set $\{\psi:P_\psi(h,b)=z\}$ is Borel. The maximum is a supremum, and the second clause states that it is attained.
--
--   Differences from the source:
--   - generalization: a verifier whose classical messages alternate (p.9) and whose outgoing message registers are measured in the computational basis (p.8) → a `Verifier`: any finite list of unitary steps, controlled queries, verifier messages given by any instrument $\{K_a\}$ with $\sum_a K_a^\dagger K_a=I$, and padded prover messages received through unitaries, in any order; reason: the paper's verifiers are instances (alternation is a convention that padding makes harmless, p.9; measuring a register in the computational basis is $K_a=|a\rangle\langle a|\otimes I$)
--   - encoding: private quantum registers and private measurements; controlled and uncontrolled oracle calls → pure states on $\{0,1\}\times[D]\times W$ for a finite workspace $W$ with private measurements deferred; every call controlled; reason: the paper defers private measurements (p.10) and allows controlled calls (p.8); an uncontrolled call is a controlled one with the control set to $|1\rangle$
--   - encoding: Borel measurability of the choice on $\mathbb{CP}^{D-1}$; $\max_P$ → `IsMeasurableProverFamily` on $\mathbb C^D$; $\sup_P$ attained at $P_\psi$; reason: same statement for the family on the sphere's ambient space
-- source:
--   Barhoush, Quantum State Search with Classical Interactive Advice, arXiv:2610.25657 (held version, sha256 2a16939a…3408), proof of Theorem 4, first paragraph, p.13

import Mathlib
import Definitions.Def_QStateSearch_Verifier
import Definitions.Def_QStateSearch_AccW
import Definitions.Def_QStateSearch_refl
import Definitions.Def_QStateSearch_IsMeasurableProverFamily

namespace QStateSearch

/-- **Proof of Theorem 4, measurable maximizer.** (i) For each fixed deterministic prover `P`,
`ψ ↦ Acc_{R_ψ}(V, P)` is continuous. (ii) There is a measurable choice `ψ ↦ P_ψ` of deterministic
provers maximizing `|Acc_{R_ψ}(V, P) − Acc_I(V, P)|` for every `ψ` (so the maximum is attained).

Barhoush, *Quantum State Search with Classical Interactive Advice*, arXiv:2610.25657
(held version, sha256 2a16939a…3408), proof of Theorem 4, first paragraph, p.13.

**Formalization Note.** Measurability of the family is `IsMeasurableProverFamily` (every set
`{ψ | P_ψ(h, b) = z}` is Borel). The maximum over provers is `⨆ P`; clause (ii) says it is
attained at `P_ψ`. -/
theorem measurable_maximizer {D : ℕ} {W : Type} [Fintype W] [DecidableEq W] (V : Verifier D W) :
    (∀ P : Prover, Continuous fun ψ : EuclideanSpace ℂ (Fin D) => AccW V (refl ψ) P) ∧
    ∃ Pm : EuclideanSpace ℂ (Fin D) → Prover, IsMeasurableProverFamily Pm ∧
      ∀ ψ, |AccW V (refl ψ) (Pm ψ) - AccW V 1 (Pm ψ)| =
        ⨆ P : Prover, |AccW V (refl ψ) P - AccW V 1 P| := by sorry

end QStateSearch
