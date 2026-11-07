-- Prove2me | Theorems.Thm_SysBathGibbs_lemma_8_5
-- name    : SysBathGibbs.lemma_8_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:38:24.094196+00:00
-- url     : https://prove2.me/theorems/604bc87d-2d16-483e-b016-0797e929432a
-- title:
--   Lemma 8.5 — The same-time Lamb shift form
-- statement:
--   There is $C>0$, depending only on $\beta$ and $q$ ($\sigma=\beta/2$), such that for every chain (1.2) on $n\ge1$ sites, every $T_0\ge1$ and every traceless $X$, with $Y_T=\mathcal U(T)X$ and $T\sim\mu_{T_0}$,
--   $$
--   \Big|2\,\mathbb E_T\operatorname{Re}\big\langle\Gamma^{-1}(Y_T),\Gamma^{-1}(\mathcal Q_{\mathrm{Lamb}}Y_T)\big\rangle_{\rho_\beta}\Big|\le C\sqrt{n\,\mathcal E_\mu(X)\mathcal D_\mu(X)}+Cn\,\mathcal D_\mu(X).
--   $$
--
--   The Lamb-shift contribution to one step of the ideal channel is controlled by the dephasing and dissipation it competes with.
--
--   Differences from the source:
--   - encoding: σ a free parameter of (1.4)–(1.8) → σ = β/2 throughout; reason: the paper fixes σ = β/2 throughout (p.10); no other width is stated
--   - encoding: a chain [n] of qudits of dimension 2^q → n ≥ 1 and q ≥ 1 as hypotheses; reason: a chain has a site and a qudit has q ≥ 1 qubits; Q = 4^q − 1 ≥ 1 is used throughout
--   - reading: constants C, c depending on the fixed local parameters β, q (p.10) → ∃ constants after β and q, before n and the chain; reason: §2.1: constants depend on β, q but not on n, α, T, T0; the proof uses only (1.2)
-- source:
--   Ding, Li, Zhang, Efficient thermalization of one-dimensional noncommuting Hamiltonians via system-bath interactions with Θ(n) ancilla qubits, arXiv:2611.03422 (held file sha256 a60a3c09826df3b5399a5589f83ef3a1d2ea768d74c5e39e8a3b29d1323f024f), Lemma 8.5 (eq. (8.10)), p.63

import Definitions.Def_SysBathGibbs_Contraction

open Matrix MeasureTheory

namespace SysBathGibbs

/-- **Lemma 8.5 (The same-time Lamb shift form)**, Ding, Li, Zhang, arXiv:2611.03422 (held file sha256 a60a3c09…), p.63.
Let `X` be traceless and `Y_T = U(T)X`. For every `T₀ ≥ 1`,
`|2 E_T Re⟨Γ⁻¹(Y_T), Γ⁻¹(Q_Lamb Y_T)⟩_{ρ_β}| ≤ C√(nE_μ(X)D_μ(X)) + CnD_μ(X)`.

**Formalization Note.** `E_T` is over `μ_{T₀}`, and `C` depends on `β, q` only (§2.1, p.10). -/
theorem lemma_8_5 :
    ∀ (β : ℝ), 0 < β → ∀ q : ℕ, 1 ≤ q →
      ∃ C : ℝ, 0 < C ∧
        ∀ (n : ℕ), 1 ≤ n → ∀ h : Fin (n - 1) → SysMat n q, IsChain h →
          ∀ T₀ : ℝ, 1 ≤ T₀ → ∀ X : SysMat n q, Matrix.trace X = 0 →
            |2 * ∫ T, (kmsInner β (chainHam h)
                  (Gam β (chainHam h) (-1) (fwd (chainHam h) T X))
                  (Gam β (chainHam h) (-1) (QLamb β h (fwd (chainHam h) T X)))).re ∂(timeLaw T₀)| ≤
              C * Real.sqrt (n * Emu β h T₀ X * Dmu β h T₀ X) + C * n * Dmu β h T₀ X := by sorry

end SysBathGibbs
