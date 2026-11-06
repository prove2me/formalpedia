-- Prove2me | Theorems.Thm_SpinGirth5_proposition_29_psi_formula
-- name    : SpinGirth5.proposition_29_psi_formula
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:12:53.039384+00:00
-- url     : https://prove2.me/theorems/28bc61af-f7f5-44d3-b121-f4882d01edbb
-- title:
--   Proposition 29 — $\Psi_i=\operatorname{diag}(1-Bp_i)^{-1}B(\operatorname{diag}(p_i)-p_ip_i^\top)B\operatorname{diag}(1-Bp_i)^{-1}$
-- statement:
--   Let $(A,\lambda)$ be a multi-spin system with deficit matrix $B=\mathbf 1\mathbf 1^\top-A$, and let $p=p_i$ be a probability distribution on $[q]$ with $(Ap)(\mathfrak c)>0$ for every colour $\mathfrak c$. With $L^{\mathfrak c}_i(\mathfrak a)=A_{\mathfrak c,\mathfrak a}/(Ap_i)(\mathfrak c)$ and $\Psi_i(\mathfrak c,\mathfrak d)=\operatorname{Cov}_{p_i}(L^{\mathfrak c}_i,L^{\mathfrak d}_i)$,
--   $$\Psi_i=\operatorname{diag}(1-Bp_i)^{-1}\,B\,\big(\operatorname{diag}(p_i)-p_ip_i^{\top}\big)\,B\,\operatorname{diag}(1-Bp_i)^{-1}.$$
--   The matrix $\Psi_i$ measures the influence of the centre on leaf $i$; this closed form is what Corollary 30 estimates.
--
--   Differences from the source:
--   - encoding: L^𝔠_i(𝔞) = A_{𝔠,𝔞}/(A p_i)(𝔠), defined implicitly → hypothesis (A p)(𝔠) > 0 for every 𝔠; reason: otherwise L^𝔠_i is undefined; under the standing assumptions (A p_i)(𝔠) ≥ 1 − α/Δ ≥ 1/2 (p.22)
--   - generalization: p_i = µ^τ_{G−v,i} for a leaf i of the star (13) → any probability distribution p on [q]; reason: the identity is algebraic and uses only that p sums to 1 and A is symmetric
-- source:
--   Chen, Liu, A Spectral Local-to-Global Principle for Spin Systems on Graphs with Girth At Least Five, arXiv:2608.25491, Proposition 29, p.22

import Mathlib
import Definitions.Def_SpinGirth5_starModel

namespace SpinGirth5

open Matrix

/-- **Proposition 29**. For a leaf law `p = p_i` (a distribution on `[q]`) with `(A p)(c) > 0` for
every colour `c`,
`Ψ_i = diag(1 − B p_i)⁻¹ B (diag(p_i) − p_i p_iᵀ) B diag(1 − B p_i)⁻¹`,
where `Ψ_i(c, d) = Cov_{p_i}(L^c_i, L^d_i)`, `L^c_i(a) = A_{c,a}/(A p_i)(c)` and `B = 11ᵀ − A`.

Chen, Liu, *A Spectral Local-to-Global Principle for Spin Systems on Graphs with Girth At Least
Five*, arXiv:2608.25491, Proposition 29, p.22.

**Formalization Note** The hypothesis `(A p)(c) > 0` makes `L^c_i` defined (the paper has
`(A p_i)(c) ≥ 1 − α/Δ ≥ 1/2` under its standing assumptions, p.22). `diag(v)⁻¹` is the diagonal
matrix of the entrywise inverses. -/
theorem proposition_29_psi_formula {q : ℕ} (S : Interaction q) (p : Fin q → ℝ)
    (hp : MarkovMixing.IsDist p) (hAp : ∀ c, 0 < (S.A *ᵥ p) c) :
    Psi S.A p =
      diagonal (fun c => (1 - (S.B *ᵥ p) c)⁻¹) * S.B * (diagonal p - vecMulVec p p) * S.B *
        diagonal (fun c => (1 - (S.B *ᵥ p) c)⁻¹) := by sorry

end SpinGirth5
