-- Prove2me | Theorems.Thm_QPSpinProfile_lemma_2_5
-- name    : QPSpinProfile.lemma_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T03:27:44.263521+00:00
-- url     : https://prove2.me/theorems/cc39ef76-6db4-4206-9d86-41c88cf6b2ed
-- title:
--   Lemma 2.5: uniform cost of a conditioning budget
-- statement:
--   There is a universal constant $C<\infty$ such that for every $n,p\ge2$ and $0\le m_\star\le n-p$,
--   $$
--   \mathbb E\max_{J\in\mathcal J_{n,m_\star}}\|H_{\mathrm{hit}}(J^c)\|_{\mathrm{op}}\le C\,3^{p/2}\sqrt{p\,m_\star}, \tag{22}
--   $$
--   where $\mathcal J_{n,m_\star}=\{J\subseteq[n]:|J^c|\le m_\star\}$ and $H_{\mathrm{hit}}(J^c)$ is the part of $H_{n,p}$ whose interactions meet $J^c$.
--
--   The maximum is inside the expectation: the bound controls all admissible sets simultaneously, which is what the energy comparison of Lemma 2.6 needs when $J$ depends on the state.
--
--   Differences from the source:
--   - encoding: Pauli strings $P^a_I$ and independent standard Gaussian coefficients $g_P$ → words $w : \mathrm{Fin}\,n \to \mathrm{Fin}\,4$ with exactly $p$ non-identity letters; the disorder is a vector $g \in \mathbb R^{\mathcal P_{n,p}}$ with law $\bigotimes_P N(0,1)$; reason: bijection with the pairs $(I, a)$; same model
--   - encoding: $\mathbb E\max_J\|H_{\mathrm{hit}}(J^c)\|_{\mathrm{op}}$ → lower Lebesgue integral of the maximum of the nonnegative norms; reason: the integrand is nonnegative, so this is its expectation with no hidden integrability condition
--   - encoding: $\|\cdot\|_{\mathrm{op}}$ → published `opNormInf` (largest singular value); reason: equal
--   - encoding: $3^{p/2}$; $0\le m_\star\le n-p$ for integers → $(\sqrt3)^p$; $p\le n$ and $m_\star\le n-p$ in $\mathbb N$; reason: equal; same range
-- source:
--   Al-Ghattas, Gamarnik, Kiani, Beyond light cones: State preparation complexity in quantum spin glasses, arXiv:2610.02166 (held version, sha256 a0a1ec89…), Lemma 2.5, p.23 (PDF p.26), display (22)

import Mathlib
import Definitions.Def_DeFinettiSDP_Hierarchy_Systems
import Definitions.Def_QPSpinProfile_Hhit

namespace QPSpinProfile

open MeasureTheory

/-- **Lemma 2.5 (Uniform cost of a conditioning budget)** (Al-Ghattas, Gamarnik, Kiani, *Beyond light cones: State preparation complexity in quantum spin glasses*, arXiv:2610.02166 (held version, sha256 a0a1ec89…), p.23, PDF p.26).
There is a universal constant `C` such that for every `n, p ≥ 2` and `0 ≤ m⋆ ≤ n − p`, (22):
`E max_{J ∈ J_{n,m⋆}} ‖H_hit(Jᶜ)‖_op ≤ C 3^{p/2} √(p m⋆)`.

**Formalization Note** The maximum of the nonnegative norms is taken inside the expectation, which
is a lower Lebesgue integral in `[0, ∞]` (no integrability assumption is hidden). `‖·‖_op` is the
published `DeFinettiSDP.Hierarchy.opNormInf` (largest singular value); `3^{p/2} = (√3)^p`. The
integer range `0 ≤ m⋆ ≤ n − p` is written `p ≤ n`, `m⋆ ≤ n − p`. -/
theorem lemma_2_5 : ∃ C : ℝ, 0 < C ∧
    ∀ (n p m : ℕ), 2 ≤ p → p ≤ n → m ≤ n - p →
      ∫⁻ g, (admissible n m).sup
          (fun J => ENNReal.ofReal (DeFinettiSDP.Hierarchy.opNormInf (Hhit n p J g)))
        ∂(gaussMeasure n p)
        ≤ ENNReal.ofReal (C * Real.sqrt 3 ^ p * Real.sqrt ((p : ℝ) * m)) := by sorry

end QPSpinProfile
