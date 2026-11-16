-- Prove2me | Theorems.Thm_TreeCoverLB_Supplement_theorem_7_2
-- name    : TreeCoverLB.Supplement.theorem_7_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:24:04.371999+00:00
-- url     : https://prove2.me/theorems/5ebcb565-35da-4347-9a26-33b64d383800
-- title:
--   Theorem 7.2 — $\mathrm{ind}^{(H)}_{\mathcal K}(X)\ge\mathrm{ind}_H(X)\ge\mathrm{ind}_{\mathbb Z_p}(|I_{p,k}|)$ for every prime $p\mid|H|$
-- statement:
--   Let $H$ be a finite nontrivial group, and let $D,k\ge 1$ be integers. Let $\mathcal K=(K_d)_{d\ge D}$ be a family of finite abstract simplicial complexes. Suppose that for every $d\ge D$:
--
--   1. $\dim K_d\le d$, so every face has at most $d+1$ vertices;
--   2. $H$ acts simplicially on $K_d$, and the induced action on $|K_d|$ is free.
--
--   Let $A_1,\dots,A_k$ be nonempty finite alphabets. Suppose $H$ acts simplicially on the agreement complex $I(A_1,\dots,A_k)$ and freely on $X:=|I(A_1,\dots,A_k)|$. Then for every prime $p$ dividing $|H|$,
--   $$
--   \operatorname{ind}^{(H)}_{\mathcal K}(X)\ \ge\ \operatorname{ind}_H(X)\ \ge\ \operatorname{ind}_{\mathbb Z_p}(|I_{p,k}|).
--   $$
--   Here $\operatorname{ind}^{(H)}_{\mathcal K}(X)$ is the least $d\ge D$ for which a continuous $H$-equivariant map $X\to|K_d|$ exists, and $\operatorname{ind}_H(X)$ the least $d\ge 0$ for which a continuous $H$-equivariant map $X\to|E_dH|$ exists (each $+\infty$ when there is none; Definitions 7.1 and 4.2).
--
--   The complexes $K_d$ are the spaces a hard instance in the style of §4 could be built on, and the alphabets are the labels of the $k$ trees. With Theorem 6.1 this shows that no such choice gives a tree-cover lower bound better than $n^{O(1/k^{\log_3 4})}$.
--
--   **Formalization Note** Each inequality is stated as an implication between the existence of maps:
--   1. for every $d\ge D$, a continuous $H$-equivariant map $X\to|K_d|$ yields one $X\to|E_dH|$;
--   2. for every prime $p\mid|H|$ and every $d$, a continuous $H$-equivariant map $X\to|E_dH|$ yields a continuous $\mathbb Z_p$-equivariant map $|I_{p,k}|\to|E_d\mathbb Z_p|$.
--
--   $H$ is written additively and need not be commutative. The family is indexed by all $d\in\mathbb N$, but only the members with $d\ge D$ are constrained or used. An action on a complex is an action on its vertex type that maps faces to faces, extended linearly to the realization. The action of $H$ on the words is arbitrary; it is not assumed to act coordinatewise. Maps are functions on the ambient coordinate spaces that are continuous on the source realization, map it into the target realization, and are equivariant at every point of it.
--
--   Differences from the source:
--   - encoding: ind^{(H)}_K(X) ≥ ind_H(X) ≥ ind_{ℤ_p}(|I_{p,k}|) → for every d ≥ D a map X → |K_d| yields a map X → |E_dH|, and for every d a map X → |E_dH| yields a map |I_{p,k}| → |E_dℤ_p|; reason: E_dG ⊆ E_{d'}G equivariantly for d ≤ d', so the sets defining ind_H and ind_{ℤ_p} are upward closed and each inequality of infima is equivalent to the implication
--   - reading: finite alphabets A_1, …, A_k → finite and nonempty alphabets; reason: I(A_1, …, A_k) is defined in Definition 4.1 for nonempty finite alphabets only; with an empty alphabet X = ∅ and the second inequality fails for k ≥ 3 by Theorem 6.1
--   - encoding: a family (K_d)_{d≥D} → a family indexed by all d ∈ ℕ whose members with d < D are unconstrained and unused; reason: any family on d ≥ D extends to ℕ, and the statement only mentions d ≥ D
--   - encoding: a finite nontrivial group H written multiplicatively → an additive group (`AddGroup H`, not assumed commutative) acting by `+ᵥ`, with its action on realizations by `ptAct` and on |E_dH| by `ejoinAct`; reason: the base mission's convention; every group is the additive copy of a multiplicative one, so no instance changes
-- source:
--   Chen, Huang, Tan, Xu, Improved Lower Bounds on Tree Covers, arXiv:2607.27264 (version of October 31, 2026), Theorem 7.2, p.29 (PDF p.31); setting of §7 and Definition 7.1, p.29 (PDF p.31); Definitions 4.1, 4.2, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_TreeCoverLB_realization
import Definitions.Def_TreeCoverLB_EJoin
import Definitions.Def_TreeCoverLB_agreementComplex
import Definitions.Def_TreeCoverLB_IsAgreementIndexMap
import Definitions.Def_TreeCoverLB_Supplement_agreementComplexGen

open Classical

namespace TreeCoverLB.Supplement

/-- **Theorem 7.2** (Chen, Huang, Tan, Xu, *Improved Lower Bounds on Tree Covers*,
arXiv:2607.27264 (version of October 31, 2026), Theorem 7.2, p.29 (PDF p.31); setting of §7 and
Definition 7.1, p.29): let `H` be a finite nontrivial group, `D, k ≥ 1`, and `K = (K_d)_{d ≥ D}` a
family of finite ASCs with `dim K_d ≤ d` and a simplicial `H`-action free on `|K_d|`. Let
`A_1, …, A_k` be (nonempty) finite alphabets, and suppose `H` acts simplicially on
`I(A_1, …, A_k)` and freely on `X := |I(A_1, …, A_k)|`. Then for every prime `p ∣ |H|`,
`ind^{(H)}_K(X) ≥ ind^{(H)}_H(X) ≥ ind^{(ℤ_p)}_{ℤ_p}(|I_{p,k}|)`.

**Formalization Note** The indices are infima of the `d` admitting a continuous equivariant map
(`+∞` if none). Since `E_dG ⊆ E_{d'}G` equivariantly for `d ≤ d'`, the sets defining `ind_H` and
`ind_{ℤ_p}` are upward closed, so the two inequalities are equivalent to the two implications
stated: (1) for every `d ≥ D`, a continuous `H`-equivariant map `X → |K_d|` yields one
`X → |E_dH|`; (2) for every prime `p ∣ |H|` and every `d`, a continuous `H`-equivariant map
`X → |E_dH|` yields a continuous `ℤ_p`-equivariant map `|I_{p,k}| → |E_dℤ_p|`.
`H` is written additively (not necessarily commutative). The family is indexed by all `d : ℕ`
but only its members with `d ≥ D` are constrained or used. A simplicial action is an action on
the vertex type that maps faces to faces; it acts on realizations by `ptAct`; "free on `|K|`"
means no nonzero `h` fixes a point of `|K|`; `dim K_d ≤ d` means every face has at most `d + 1`
vertices. The action of `H` on the words is arbitrary (not assumed coordinatewise). Maps are
functions on the ambient coordinate spaces, continuous on, mapping into, and equivariant on the
realizations. -/
theorem theorem_7_2
    {H : Type*} [AddGroup H] [Fintype H] [Nontrivial H]
    (D : ℕ) (hD : 1 ≤ D)
    (V : ℕ → Type*) [∀ d, Fintype (V d)] [∀ d, AddAction H (V d)]
    (K : ∀ d, Set (Finset (V d)))
    (hK : ∀ d, D ≤ d → IsASC (K d))
    (hKdim : ∀ d, D ≤ d → ∀ σ ∈ K d, σ.card ≤ d + 1)
    (hKsimp : ∀ d, D ≤ d → ∀ h : H, ∀ σ ∈ K d, σ.image (fun v => h +ᵥ v) ∈ K d)
    (hKfree : ∀ d, D ≤ d → ∀ h : H, ∀ μ ∈ realization (K d), ptAct h μ = μ → h = 0)
    (k : ℕ) (hk : 1 ≤ k)
    (A : Fin k → Type*) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)] [∀ i, Nonempty (A i)]
    [AddAction H (∀ i, A i)]
    (hAsimp : ∀ h : H, ∀ σ ∈ agreementComplexGen A,
      σ.image (fun x => h +ᵥ x) ∈ agreementComplexGen A)
    (hAfree : ∀ h : H, ∀ μ ∈ realization (agreementComplexGen A),
      ptAct h μ = μ → h = 0) :
    (∀ d, D ≤ d →
      (∃ F : ((∀ i, A i) → ℝ) → (V d → ℝ),
        ContinuousOn F (realization (agreementComplexGen A)) ∧
        Set.MapsTo F (realization (agreementComplexGen A)) (realization (K d)) ∧
        ∀ h : H, ∀ μ ∈ realization (agreementComplexGen A),
          F (ptAct h μ) = ptAct h (F μ)) →
      ∃ G : ((∀ i, A i) → ℝ) → (Fin (d + 1) × H → ℝ),
        ContinuousOn G (realization (agreementComplexGen A)) ∧
        Set.MapsTo G (realization (agreementComplexGen A))
          (realization (EJoin d H)) ∧
        ∀ h : H, ∀ μ ∈ realization (agreementComplexGen A),
          G (ptAct h μ) = ejoinAct h (G μ)) ∧
    (∀ p : ℕ, ∀ hp : p.Prime, p ∣ Fintype.card H → ∀ d : ℕ,
      (∃ G : ((∀ i, A i) → ℝ) → (Fin (d + 1) × H → ℝ),
        ContinuousOn G (realization (agreementComplexGen A)) ∧
        Set.MapsTo G (realization (agreementComplexGen A))
          (realization (EJoin d H)) ∧
        ∀ h : H, ∀ μ ∈ realization (agreementComplexGen A),
          G (ptAct h μ) = ejoinAct h (G μ)) →
      ∃ ψ : ((Fin k → ZMod p) → ℝ) → (Fin (d + 1) × ZMod p → ℝ),
        haveI : Fact p.Prime := ⟨hp⟩
        IsAgreementIndexMap p k d ψ) := by sorry

end TreeCoverLB.Supplement
