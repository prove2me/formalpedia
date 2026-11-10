-- Prove2me | Theorems.Thm_TolProdTest_claim_2_1
-- name    : TolProdTest.claim_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T03:27:19.359348+00:00
-- url     : https://prove2.me/theorems/2320872e-da8a-45e7-b5cb-01223f2214a7
-- title:
--   Claim 2.1 — completeness: $Z_k(\rho)\ge F_{\mathrm{prod}}(\rho)^k$
-- statement:
--   Let $n\ge1$, $d\ge2$ and let $\rho$ be a density operator on $(\mathbb C^d)^{\otimes n}$. For every integer $k\ge2$, the $k$-copy product test accepts $\rho$ with probability
--
--   $$
--   Z_k(\rho)\ \ge\ F_{\mathrm{prod}}(\rho)^k .
--   $$
--
--   This is the completeness of the test: states close to a product state are accepted with probability at least the $k$-th power of their product fidelity, including mixed inputs.
--
--   Differences from the source:
--   - encoding: ρ ∈ D((ℂ^d)^{⊗n}), n ≥ 1, d ≥ 2 → ρ : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ with WildeQIT.IsDensityOperator ρ (positive semidefinite, trace 1); reason: the computational basis of (ℂ^d)^{⊗n} is indexed by level strings Fin n → Fin d; same operators, sites and levels 0-based
--   - encoding: F_prod(ρ) as a maximum over unit vectors |π_i⟩ ∈ ℂ^d (2) → fprod ρ, the supremum of Re⟨π_1⊗⋯⊗π_n|ρ|π_1⊗⋯⊗π_n⟩ over families of unit vectors; reason: the set is nonempty and bounded and the supremum is attained (compactness); the form is real for Hermitian ρ, so the value is the printed maximum
--   - encoding: Z_k(ρ) = Tr[Q_k ρ^{⊗k}], Q_k the product of the projectors onto Sym^k(H_i) (20)–(21) → zk ρ k = Re Tr[Q_k ρ^{⊗k}], with Q_k the average over σ : Fin n → S_k of the operators permuting the k copies of each site i by σ_i; reason: (1/k!) Σ_π P_π is the orthogonal projector onto Sym^k and the site projectors commute, so the average is ∏_i Q_{k,i}; the trace is real for ρ ≥ 0
-- source:
--   Bao, Helsen, Nguyen, Fully tolerant product state testing and closest product state learning, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), Claim 2.1, p.9

import Mathlib
import Definitions.Def_TolProdTest_fprod
import Definitions.Def_TolProdTest_zk
import Definitions.Def_WildeQIT_IsDensityOperator

set_option autoImplicit false

open Matrix

namespace TolProdTest

/-- **Claim 2.1 (completeness of the k-copy product test)**, Bao, Helsen, Nguyen, *Fully tolerant product state testing and closest product state learning*, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), p.9: "For any k ≥ 2, Z_k(ρ) ≥ F_prod(ρ)^k."

Standing assumptions (§1, p.2): `n ≥ 1`, `d ≥ 2`, `ρ ∈ D((ℂ^d)^{⊗n})`. -/
theorem claim_2_1 {n d : ℕ} (hn : 1 ≤ n) (hd : 2 ≤ d) (k : ℕ) (hk : 2 ≤ k)
    (ρ : Matrix (Config n d) (Config n d) ℂ) (hρ : WildeQIT.IsDensityOperator ρ) :
    fprod ρ ^ k ≤ zk ρ k := by sorry

end TolProdTest
