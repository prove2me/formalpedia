-- Prove2me | Theorems.Thm_UnitalMIP_lemma_4_1
-- name    : UnitalMIP.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:42:13.016237+00:00
-- url     : https://prove2.me/theorems/6295ceba-4147-4e25-b976-f871150cc6b3
-- title:
--   Lemma 4.1 — complete strong data-processing inequality for $\mathcal K_{\psi_{\boldsymbol\lambda}}$
-- statement:
--   Let $\psi\in M_2\otimes M_2$ be a state with $\psi_A=\psi_B=\mathbb 1/2$ and $\rho_{\max}(\psi)<1$. There is a constant $0\le\alpha_\psi<1$, depending only on $\psi$, such that for every canonical form $\psi_{\boldsymbol\lambda}$ of $\psi$, every $m\ge1$ and every density matrix $\rho\in M_m\otimes M_2$,
--
--   $$
--   D\bigl((\mathrm{id}_{M_m}\otimes\mathcal K_{\psi_{\boldsymbol\lambda}})(\rho)\,\big\|\,(\mathrm{id}_{M_m}\otimes\Pi)(\rho)\bigr)\le\alpha_\psi\,D\bigl(\rho\,\big\|\,(\mathrm{id}_{M_m}\otimes\Pi)(\rho)\bigr),
--   $$
--
--   where $\Pi(X)=\tau_2(X)\mathbb 1$. The same coefficient works for every ancilla dimension $m$.
--
--   This contraction of relative entropy is what bounds the loss of game value under smoothing (Theorem 3.2).
--
--   **Formalization Note** Relative entropy uses the natural logarithm (the published `LindenReversibility.relEntropy`).
--
--   Differences from the source:
--   - reading: “Choose a canonical form ψλ of ψ … There is a constant αψ, depending only on ψ” → one constant $\alpha_\psi$ that works for every canonical form of $\psi$; reason: the source does not say whether $\alpha_\psi$ is tied to the chosen form; two canonical forms differ by local unitaries, under which the inequality is invariant, and the constant is said to depend only on $\psi$; this is the stronger reading
--   - generalization: the §1.1 standing assumption (“Throughout, let ψ be a fixed two-qubit state … and assume that its entries are computable in polynomial time”, p.4) → any two-qubit density matrix ψ with the stated properties, with no computability hypothesis; reason: the statement is purely analytic and holds for every such state; it specializes to the source's claim on every computable ψ
-- source:
--   Dong, Jiang, Qin, Yao, Zhou, A Dichotomy for MIP* in the Presence of Unital Noise, arXiv:2609.39318 (version of 2026-11-03, sha256 56ebc59e…), Lemma 4.1, p.32

import Mathlib
import Definitions.Def_UnitalMIP_HasMaxMixedMarginals
import Definitions.Def_UnitalMIP_rhoMax
import Definitions.Def_UnitalMIP_IsCompleteSDPIConst

open scoped Matrix

namespace UnitalMIP

/-- **Lemma 4.1** (Complete SDPI; Dong, Jiang, Qin, Yao, Zhou, *A Dichotomy for MIP* in the Presence of Unital Noise*, arXiv:2609.39318 (version of 2026-11-03, sha256 56ebc59e…), p.32). Let `ψ ∈ M₂ ⊗ M₂` satisfy `ψ_A = ψ_B = 𝟙/2` and
`ρmax(ψ) < 1`. There is a constant `0 ≤ α_ψ < 1`, depending only on `ψ`, such that for every
canonical form `ψ_λ` of `ψ`, every `m ≥ 1` and every density matrix `ρ ∈ M_m ⊗ M₂`,
`D((id ⊗ K_{ψ_λ})(ρ) ‖ (id ⊗ Π)(ρ)) ≤ α_ψ D(ρ ‖ (id ⊗ Π)(ρ))`.

**Formalization Note** The inequality is `IsCompleteSDPIConst ψ α` (relative entropy with the
natural logarithm, the published `LindenReversibility.relEntropy`). "Choose a canonical form" is read as "for every canonical
form", with one constant for all of them: canonical forms differ by local unitaries, under which
the inequality is invariant, and the source says the constant depends only on `ψ`. -/
theorem lemma_4_1 (ψ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hψ : QAlgorithms.IsDensityMatrix ψ) (hmm : HasMaxMixedMarginals ψ) (hρ : rhoMax ψ < 1) :
    ∃ α : ℝ, 0 ≤ α ∧ α < 1 ∧ IsCompleteSDPIConst ψ α := by sorry

end UnitalMIP
