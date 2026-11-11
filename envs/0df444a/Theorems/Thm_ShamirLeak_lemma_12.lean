-- Prove2me | Theorems.Thm_ShamirLeak_lemma_12
-- name    : ShamirLeak.lemma_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:13:10.012091+00:00
-- url     : https://prove2.me/theorems/42aac508-bfe6-4200-81d9-7b3db232218f
-- title:
--   Lemma 12 — a product of Gowers norms
-- statement:
--   Fix a prime $p$, integers $k\ge2$ and $r\ge1$, and write $V=\mathbb F_p^{k-1}$. Let $\Psi=(b_i+L_i)_{i=1}^r$ be a system of affine-linear forms on $V$ and $f_i:\mathbb F_p\to\mathbb C$. Suppose $[r]=J\sqcup I_1\sqcup\dots\sqcup I_t$ with $t\ge2$, and the linear parts indexed by $I_a\cup J$ are independent for every $a$. Then
--
--   $$|\Lambda_\Psi(f)|\le\prod_{j\in J}\|f_j\|_{U^t}\prod_{i\in[r]\setminus J}\|f_i\|_\infty.$$
--
--   This is a form of Manners's generalized von Neumann inequality for vector-valued linear maps; grouping forms into one map yields a product of Gowers norms.
--
--   **Formalization Note** The partition is a set $J$ and blocks $I_1,\dots,I_t$, pairwise disjoint, with union all indices; empty blocks are allowed.
--
--   Differences from the source:
--   - generalization: p an odd prime (§2 standing assumption) → every prime p (as in the preamble of §5.1); reason: §5.1 fixes an arbitrary prime and the argument does not use oddness; it specializes to odd p
-- source:
--   Nguyen, Local Leakage Resilience of Shamir Secret Sharing: Below Half Threshold Rate, arXiv:2610.17711 (version of 2026-11-03, sha256 6ba85290…), Lemma 12, p.24 (PDF 26); §5.1 preamble and Definitions 12–13, p.23

import Mathlib
import Definitions.Def_ShamirLeak_chi
import Definitions.Def_ShamirLeak_gowersNorm
import Definitions.Def_ShamirLeak_formAvg

namespace ShamirLeak

/-- **Lemma 12 (A product of Gowers norms)**, p.24 (PDF p.26). Fix a prime `p`, integers `k ≥ 2` and
`r ≥ 1`, and write `V = 𝔽_p^{k−1}`. Let `Ψ = (bᵢ + Lᵢ)_{i=1}^r` be a system on `V`, and let
`fᵢ : 𝔽_p → ℂ`. Suppose `[r] = J ⊔ I₁ ⊔ ⋯ ⊔ I_t`, with `t ≥ 2`, and the linear parts indexed by
`I_a ∪ J` are independent for every `a`. Then `|Λ_Ψ(f)| ≤ ∏_{j∈J} ‖f_j‖_{U^t} ∏_{i∈[r]∖J} ‖fᵢ‖_∞`.
H. H. Nguyen, *Local Leakage Resilience of Shamir Secret Sharing: Below Half Threshold Rate*,
arXiv:2610.17711 (version of 2026-11-03, sha256 6ba85290…), Lemma 12, p.24 (PDF p.26); preamble of §5.1 and Definitions 12–13, p.23.

**Formalization Note.** The partition is given by `J` and `I : Fin t → Finset (Fin r)`, pairwise
disjoint, with union all of `Fin r`; empty blocks are allowed and the empty family counts as
independent (p.23). `p` is any prime, as in the preamble of §5.1. -/
theorem lemma_12 {p k r : ℕ} [Fact p.Prime] (hk : 2 ≤ k) (hr : 1 ≤ r)
    (L : Fin r → (Fin (k - 1) → ZMod p)) (b : Fin r → ZMod p) (f : Fin r → ZMod p → ℂ)
    (t : ℕ) (ht : 2 ≤ t) (J : Finset (Fin r)) (I : Fin t → Finset (Fin r))
    (hII : ∀ a a', a ≠ a' → Disjoint (I a) (I a')) (hJI : ∀ a, Disjoint J (I a))
    (hcover : J ∪ Finset.univ.biUnion I = Finset.univ) (hind : ∀ a, IndepForms L (I a ∪ J)) :
    ‖formAvg L b f‖ ≤ (∏ j ∈ J, gowersNorm t (f j)) * ∏ i ∈ Finset.univ \ J, supNorm (f i) := by sorry

end ShamirLeak
