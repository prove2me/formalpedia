-- Prove2me | Theorems.Thm_ShamirLeak_corollary_3
-- name    : ShamirLeak.corollary_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:13:16.891367+00:00
-- url     : https://prove2.me/theorems/96954eb6-2993-4f01-9be1-835e9752f0b8
-- title:
--   Corollary 3 — number of $U^t$ factors
-- statement:
--   Let $p$ be a prime, $k\ge2$, and let $\Psi$ be an MDS system of $r$ affine-linear forms on $V=\mathbb F_p^{k-1}$ with $r\ge k$; let $t\ge2$ and
--
--   $$q_t(r,k)=\Big\lfloor\frac{t(k-1)-r}{t-1}\Big\rfloor.$$
--
--   If $q_t(r,k)\ge1$, then for every $J\subseteq[r]$ of size $q_t(r,k)$ and all $f_i:\mathbb F_p\to\mathbb C$,
--
--   $$|\Lambda_\Psi(f)|\le\prod_{j\in J}\|f_j\|_{U^t}\prod_{i\in[r]\setminus J}\|f_i\|_\infty.$$
--
--   For the coordinates of a GRS codeword and $t=3$ this retains linearly many $U^3$ factors, which drives the large-support bound (Lemma 17).
--
--   Differences from the source:
--   - generalization: p an odd prime (§2 standing assumption) → every prime p (as in the preamble of §5.1); reason: §5.1 fixes an arbitrary prime and the argument does not use oddness; it specializes to odd p
-- source:
--   Nguyen, Local Leakage Resilience of Shamir Secret Sharing: Below Half Threshold Rate, arXiv:2610.17711 (version of 2026-11-03, sha256 6ba85290…), Corollary 3, p.25 (PDF 27); §5.1 preamble, p.23

import Mathlib
import Definitions.Def_ShamirLeak_chi
import Definitions.Def_ShamirLeak_gowersNorm
import Definitions.Def_ShamirLeak_formAvg

namespace ShamirLeak

/-- **Corollary 3 (Number of `U^t` factors)**, p.25 (PDF p.27). Let `Ψ` be an MDS system on
`V = 𝔽_p^{k−1}` (`p` prime, `k ≥ 2`), let `r ≥ k` and `t ≥ 2`, and define
`q_t(r, k) = ⌊(t(k − 1) − r)/(t − 1)⌋`. If `q_t(r, k) ≥ 1`, then, for every `J ⊆ [r]` of size
`q_t(r, k)`, `|Λ_Ψ(f)| ≤ ∏_{j∈J} ‖f_j‖_{U^t} ∏_{i∈[r]∖J} ‖fᵢ‖_∞`.
H. H. Nguyen, *Local Leakage Resilience of Shamir Secret Sharing: Below Half Threshold Rate*,
arXiv:2610.17711 (version of 2026-11-03, sha256 6ba85290…), Corollary 3, p.25 (PDF p.27); preamble of §5.1 and Definitions 12–13, p.23.

**Formalization Note.** `q_t(r, k)` is the integer `qt t r k`; the size condition is
`(J.card : ℤ) = qt t r k`. `p` is any prime, as in the preamble of §5.1. -/
theorem corollary_3 {p k r : ℕ} [Fact p.Prime] (hk : 2 ≤ k)
    (L : Fin r → (Fin (k - 1) → ZMod p)) (b : Fin r → ZMod p) (f : Fin r → ZMod p → ℂ)
    (hMDS : IsMDSSystem L) (hrk : k ≤ r) (t : ℕ) (ht : 2 ≤ t) (hq : 1 ≤ qt t r k)
    (J : Finset (Fin r)) (hJ : (J.card : ℤ) = qt t r k) :
    ‖formAvg L b f‖ ≤ (∏ j ∈ J, gowersNorm t (f j)) * ∏ i ∈ Finset.univ \ J, supNorm (f i) := by sorry

end ShamirLeak
