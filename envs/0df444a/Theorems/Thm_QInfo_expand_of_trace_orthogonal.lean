-- Prove2me | Theorems.Thm_QInfo_expand_of_trace_orthogonal
-- name    : QInfo.expand_of_trace_orthogonal
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-08T23:31:03.214371+00:00
-- url     : https://prove2.me/theorems/f926ea43-993d-4cef-8b3e-93e4aaa00d40
-- title:
--   A trace-orthogonal family of $d^2$ matrices is a basis: $M = \frac1d\sum_a \mathrm{Tr}(\sigma_a M)\,\sigma_a$
-- statement:
--   Let $X$ be a finite set with $d = |X|$, and let $\{\sigma_a\}_{a\in\kappa}$ be a family of $d\times d$ complex matrices indexed by a finite set $\kappa$. Assume the family has exactly $d^2$ members and is orthogonal for the trace pairing:
--
--   $$\mathrm{Tr}(\sigma_a\sigma_b) = d\,\delta_{ab}\qquad(a,b\in\kappa),\qquad |\kappa| = d^2 .$$
--
--   Then the family is a basis of the space of $d\times d$ matrices, and every matrix $M$ has the expansion
--
--   $$M = \frac1d\sum_{a\in\kappa}\mathrm{Tr}(\sigma_a M)\,\sigma_a .$$
--
--   This is the statement, used throughout Appendix C, that a Hilbert–Schmidt basis $\{\sigma^X_\mu\}_{\mu=0}^{d_X^2-1}$ (with $\sigma_0 = \mathbb 1$, $\mathrm{Tr}\,\sigma_\mu\sigma_\nu = d_X\delta_{\mu\nu}$) spans $\mathcal L(\mathcal H^X)$, so that operators can be written as in Eqs. (16) and (18). The hypotheses are stated for an arbitrary trace-orthogonal family. They therefore apply directly to tensor products of Hilbert–Schmidt bases, such as $\sigma_\mu^{A_1}\otimes\sigma_\nu^{A_2}$, and to the Pauli or generalized Gell-Mann bases.
--
--   **Formalization Note.** For Hermitian $\sigma_a$, $\mathrm{Tr}(\sigma_a\sigma_b)$ is the Hilbert–Schmidt inner product. The statement does not assume hermiticity.
-- source:
--   O. Oreshkov, F. Costa, C. Brukner, Quantum correlations with no causal order, Nat. Commun. 3, 1092 (2012), https://arxiv.org/abs/1105.4464v3, Appendix C, p. 9: definition of a Hilbert-Schmidt basis of L(H^X) and the expansions Eqs. (16), (18)

import Mathlib

open Matrix
open scoped ComplexOrder

namespace QInfo

theorem expand_of_trace_orthogonal {X κ : Type*} [Fintype X] [DecidableEq X] [Fintype κ]
    [DecidableEq κ] (σ : κ → Matrix X X ℂ)
    (horth : ∀ a b, (σ a * σ b).trace = if a = b then (Fintype.card X : ℂ) else 0)
    (hcard : Fintype.card κ = Fintype.card X ^ 2) (M : Matrix X X ℂ) :
    M = (Fintype.card X : ℂ)⁻¹ • ∑ a, (σ a * M).trace • σ a := by sorry

end QInfo
