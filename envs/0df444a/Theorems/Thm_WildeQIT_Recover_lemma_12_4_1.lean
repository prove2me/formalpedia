-- Prove2me | Theorems.Thm_WildeQIT_Recover_lemma_12_4_1
-- name    : WildeQIT.Recover.lemma_12_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:22:03.164485+00:00
-- url     : https://prove2.me/theorems/77c6dabb-410d-4f63-8d1f-03452cbe982b
-- title:
--   Lemma 12.4.1 — $\frac{1}{\ln 2}\lim_{\alpha\to1}\widetilde\Delta_\alpha(\rho,\sigma,\mathcal N)=D(\rho\|\sigma)-D(\mathcal N(\rho)\|\mathcal N(\sigma))$
-- statement:
--   Let $\rho$ be a density operator and $\sigma$ a positive semi-definite operator on a finite-dimensional Hilbert space $\mathcal H$ with $\operatorname{supp}(\rho)\subseteq\operatorname{supp}(\sigma)$, and let $\mathcal N:\mathcal L(\mathcal H)\to\mathcal L(\mathcal H')$ be a quantum channel. Then
--
--   $$
--   \frac{1}{\ln 2}\lim_{\alpha\to1}\widetilde\Delta_\alpha(\rho,\sigma,\mathcal N)=D(\rho\|\sigma)-D(\mathcal N(\rho)\|\mathcal N(\sigma)),
--   $$
--
--   where $\widetilde\Delta_\alpha$ is the Rényi relative entropy difference of (12.56)–(12.57) and $D$ is the quantum relative entropy in bits.
--
--   This identifies $\widetilde\Delta_\alpha$ as a Rényi generalization of the relative entropy difference; it is the step that turns the interpolation bound for $\alpha\in(1/2,1)$ into the recoverability bound at $\alpha=1$.
--
--   **Formalization Note** The limit is two-sided over $\alpha\neq1$, and the constant factor $1/\ln2$ is placed inside the limit. Relative entropies are extended reals, and the limit is taken in the extended reals; under the hypotheses both relative entropies are finite. $\widetilde\Delta_\alpha$ is computed with the canonical isometric extension of the Kraus family.
--
--   Differences from the source:
--   - encoding: $\frac{1}{\ln 2}\lim_{\alpha\to1}\widetilde\Delta_\alpha$ → $\lim_{\alpha\to1,\,\alpha\ne1}\widetilde\Delta_\alpha/\ln 2$ in the extended reals; reason: a constant factor commutes with the limit, and the target is finite under the hypotheses.
--   - encoding: an arbitrary isometric extension $U$ → the canonical extension $U|\psi\rangle=\sum_l V_l|\psi\rangle\otimes|l\rangle$; reason: the book notes that $\widetilde Q_\alpha$ does not depend on the choice (p. 374).
--   - encoding: a quantum channel → a channel in Choi–Kraus form; reason: every channel has a finite Kraus form (Theorem 4.4.1).
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Lemma 12.4.1, (12.58), p. 374; definitions (12.56)–(12.57), p. 373

import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_Recover_qRelEntropy
import Definitions.Def_WildeQIT_Recover_renyiDelta
open scoped ComplexOrder
open Filter Topology

namespace WildeQIT.Recover

/-- **Lemma 12.4.1** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8,
Lemma 12.4.1, (12.58), p. 374). For `ρ`, `σ`, `𝒩` as in Definition 12.1.1,
`(1/ln 2) lim_{α→1} Δ̃_α(ρ, σ, 𝒩) = D(ρ‖σ) − D(𝒩(ρ)‖𝒩(σ))`.

**Formalization Note** The limit is two-sided, `α → 1` with `α ≠ 1`; the factor `1/ln 2` is moved
inside the limit. The limit is taken in `EReal`, where the relative entropies live; the right side
is finite under the hypotheses. `Δ̃_α` uses the canonical isometric extension of the Kraus form. -/
theorem lemma_12_4_1 {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (ρ σ : Matrix a a ℂ) (N : QChannel a b)
    (hρ : IsDensityOperator ρ) (hσ : σ.PosSemidef) (hsupp : SuppSubset ρ σ) :
    Tendsto (fun α : ℝ => ((renyiDelta ρ σ N α / Real.log 2 : ℝ) : EReal)) (𝓝[≠] 1)
      (𝓝 (qRelEntropy ρ σ - qRelEntropy (N.apply ρ) (N.apply σ))) := by sorry

end WildeQIT.Recover
