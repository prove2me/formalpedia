-- Prove2me | Theorems.Thm_TolProdTest_lemma_3_7
-- name    : TolProdTest.lemma_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T03:27:35.812202+00:00
-- url     : https://prove2.me/theorems/10cc0e95-14ba-4faa-9422-c9737ab95938
-- title:
--   Lemma 3.7 — one-trial bounds $Z_k\ge p_Y$ (YES), $Z_k\le p_N$ (NO)
-- statement:
--   Let $1\ge a>b\ge0$, $n\ge1$, $d\ge2$, and let $k$, $p_Y=a^k$, $p_N=((a+b)/2)^k$ be the parameters (67)–(69). For every density operator $\rho$ on $(\mathbb C^d)^{\otimes n}$,
--
--   $$
--   F_{\mathrm{prod}}(\rho)\ge a\ \Longrightarrow\ Z_k(\rho)\ge p_Y,\qquad
--   F_{\mathrm{prod}}(\rho)\le b\ \Longrightarrow\ Z_k(\rho)\le p_N .
--   $$
--
--   The two promised cases are separated already at the level of one trial of the $k$-copy test.
--
--   Differences from the source:
--   - encoding: ρ ∈ D((ℂ^d)^{⊗n}), n ≥ 1, d ≥ 2 → ρ : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ with WildeQIT.IsDensityOperator ρ (positive semidefinite, trace 1); reason: the computational basis of (ℂ^d)^{⊗n} is indexed by level strings Fin n → Fin d; same operators, sites and levels 0-based
--   - encoding: F_prod(ρ) as a maximum over unit vectors |π_i⟩ ∈ ℂ^d (2) → fprod ρ, the supremum of Re⟨π_1⊗⋯⊗π_n|ρ|π_1⊗⋯⊗π_n⟩ over families of unit vectors; reason: the set is nonempty and bounded and the supremum is attained (compactness); the form is real for Hermitian ρ, so the value is the printed maximum
--   - encoding: Z_k(ρ) = Tr[Q_k ρ^{⊗k}], Q_k the product of the projectors onto Sym^k(H_i) (20)–(21) → zk ρ k = Re Tr[Q_k ρ^{⊗k}], with Q_k the average over σ : Fin n → S_k of the operators permuting the k copies of each site i by σ_i; reason: (1/k!) Σ_π P_π is the orthogonal projector onto Sym^k and the site projectors commute, so the average is ∏_i Q_{k,i}; the trace is real for ρ ≥ 0
--   - encoding: the parameters c, η, q, R, k, p_Y, p_N, T of (67)–(70) with ceilings → protoC, protoEta, protoQ, protoR, protoK, protoPY, protoPN, protoT with ⌈·⌉₊ (Nat.ceil) and the natural logarithm; reason: all ceiling arguments are positive under 1 ≥ a > b ≥ 0, δ ∈ (0,1/2); log is natural (p.8)
-- source:
--   Bao, Helsen, Nguyen, Fully tolerant product state testing and closest product state learning, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), Lemma 3.7, eq. (71), p.17 (standing assumptions of §3.4, p.17)

import Mathlib
import Definitions.Def_TolProdTest_fprod
import Definitions.Def_TolProdTest_zk
import Definitions.Def_TolProdTest_protoT
import Definitions.Def_WildeQIT_IsDensityOperator

set_option autoImplicit false

open Matrix

namespace TolProdTest

/-- **Lemma 3.7 (one-trial acceptance bounds)**, Bao, Helsen, Nguyen, *Fully tolerant product state testing and closest product state learning*, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), p.17: "For the parameters in Equation (67)–Equation (69) and
any ρ ∈ D((C^d)^{⊗n}), the k-copy test satisfies F_prod(ρ) ≥ a ⟹ Z_k(ρ) ≥ p_Y, F_prod(ρ) ≤ b ⟹ Z_k(ρ) ≤ p_N. (71)"

Standing assumptions of §3.4 (p.17): `1 ≥ a > b ≥ 0`, `n ≥ 1`, `d ≥ 2`. `k = protoK a b`, `p_Y = protoPY a b`,
`p_N = protoPN a b` as in (67)–(69). -/
theorem lemma_3_7 (a b : ℝ) (hb : 0 ≤ b) (hab : b < a) (ha : a ≤ 1) {n d : ℕ} (hn : 1 ≤ n) (hd : 2 ≤ d)
    (ρ : Matrix (Config n d) (Config n d) ℂ) (hρ : WildeQIT.IsDensityOperator ρ) :
    (a ≤ fprod ρ → protoPY a b ≤ zk ρ (protoK a b)) ∧
      (fprod ρ ≤ b → zk ρ (protoK a b) ≤ protoPN a b) := by sorry

end TolProdTest
