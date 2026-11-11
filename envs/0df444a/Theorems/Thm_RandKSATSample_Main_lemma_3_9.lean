-- Prove2me | Theorems.Thm_RandKSATSample_Main_lemma_3_9
-- name    : RandKSATSample.Main.lemma_3_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:59:58.77834+00:00
-- url     : https://prove2.me/theorems/cff2b017-8118-4e11-9b06-107095b15bdf
-- title:
--   Lemma 3.9 — every deletion subformula Ψ[F] is satisfiable, µ_F(E_a) ≤ e p∗, Z_{F∖J} ≤ (1 − e p∗)^{−|J|} Z_F, Ω extends, and µ_Φ(· | V_bad ← σ) = µ_{Ψ[D_σ]}
-- statement:
--   Assume $r\ge1$ and the joint event of Lemmas 3.1 to 3.3, put $p_*=2^{-k+12}$, $C_*=10^4$, and suppose
--   $$p_*D\le\frac1{2C_*}\quad(3.4).$$
--   Then every deletion subformula $\Psi[F]$, $F\subseteq\mathcal C^{\mathrm{good}}$, is satisfiable, and for every good $a\notin F$, $\mu_F(E_a)\le e\,p_*$ (3.5). Consequently $Z_{F\setminus J}\le(1-ep_*)^{-|J|}Z_F$ for $J\subseteq F$. Moreover every $\sigma\in\Omega$ extends to a satisfying assignment of $\Phi$, and with $D_\sigma$ the good labels whose bad-variable literals are all false at $\sigma$,
--   $$\mu_\Phi(\cdot\mid V_{\mathrm{bad}}\leftarrow\sigma)=\mu_{\Psi[D_\sigma]}(\cdot).$$
--   This reduces sampling given the core to sampling the good formula.
--
--   **Formalization Note.** The conditional law is written pointwise: for every good assignment $\tau$, $\mu_\Phi(\sigma\cup\tau)/\sum_{\tau'}\mu_\Phi(\sigma\cup\tau')=\mu_{D_\sigma}(\{\tau\})$.
--
--   Differences from the source:
--   - encoding: (1 − e p∗)^{−|J|} Z_F → ((1 − e p∗)^{|J|})⁻¹ · Z_F; reason: the same number
--   - encoding: µ_Φ(· | V_bad ← σ) = µ_{Ψ[D_σ]}(·) as laws on the good variables → for every good assignment τ: µ_Φ(glue σ τ) / Σ_{τ'} µ_Φ(glue σ τ') = µ_{D_σ}({τ}); reason: equality of two laws on a finite set is equality at every point
-- source:
--   He, Li, Yang, Fast Almost-Uniform Sampling of Random k-SAT Solutions, arXiv:2610.10474 (version not printed; file sha256 563a4d84…), p. 18, Lemma 3.9

import Mathlib
import Definitions.Def_RandKSATSample_Main_Formula
import Definitions.Def_RandKSATSample_Main_Structure

set_option autoImplicit false

open scoped BigOperators

namespace RandKSATSample.Main

/-- Lemma 3.9: assume `r ≥ 1`, the joint event of Lemmas 3.1–3.3 and `p∗ D ≤ 1/(2C∗)` (3.4).
Then every deletion subformula `Ψ[F]` is satisfiable, `µ_F(E_a) ≤ e p∗` for `a ∉ F` (3.5),
`Z_{F∖J} ≤ (1 − e p∗)^{−|J|} Z_F` for `J ⊆ F`, every `σ ∈ Ω` extends to a satisfying assignment
of `Φ`, and `µ_Φ(· | V_bad ← σ) = µ_{Ψ[D_σ]}`. -/
theorem lemma_3_9 {n m k : ℕ} (Φ : Formula n m k) (hr : 1 ≤ rpar n m k) (hJ : JointEvent Φ)
    (h34 : pStar k * (Dpar n m k : ℝ) ≤ 1 / (2 * CStar)) :
    (∀ F ⊆ Cgood Φ, ∃ τ : PartAssign n (Vgood Φ), GoodEv Φ F τ) ∧
    (∀ F ⊆ Cgood Φ, ∀ a ∈ Cgood Φ, a ∉ F → muF Φ F (Viol Φ a) ≤ Real.exp 1 * pStar k) ∧
    (∀ F ⊆ Cgood Φ, ∀ J ⊆ F,
      Zf Φ (F \ J) ≤ ((1 - Real.exp 1 * pStar k) ^ J.card)⁻¹ * Zf Φ F) ∧
    (∀ σ ∈ Omega Φ, ∃ η : Assignment n, Sat Φ η ∧ ∀ v (h : v ∈ Vbad Φ), η v = σ ⟨v, h⟩) ∧
    ∀ σ ∈ Omega Φ, ∀ τ : PartAssign n (Vgood Φ),
      muPhi Φ (glue Φ σ τ) / (∑ τ' : PartAssign n (Vgood Φ), muPhi Φ (glue Φ σ τ')) =
        muF Φ (Dsig Φ σ) (fun τ' => τ' = τ) := by sorry

end RandKSATSample.Main
