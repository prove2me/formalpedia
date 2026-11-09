-- Prove2me | Theorems.Thm_QCSepTotal_theorem_4_1_eq_6
-- name    : QCSepTotal.theorem_4_1_eq_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:43:16.830521+00:00
-- url     : https://prove2.me/theorems/c640aece-9daa-486d-a083-d69eaede4080
-- title:
--   Proof of Theorem 4.1, (6) — for each $\mu$ on $\mathrm{dom}(F)$ a protocol with $CC\le CC(\Pi)+1$ and $\mathrm{err}_\mu\le\frac12-\frac\delta3$
-- statement:
--   Let $F$ be a partial function on finite sets $X\times Y$, let $c\ge1$ and $b\ge40$, let the fixed-seed maps $E_\ell$ be linear and surjective with $(u,\ell)\mapsto E_\ell(u)$ a strong $(2b,10^{-12})$-seeded extractor, and let $V$ be a certificate predicate with both valid and invalid certificates for every pair with $D_c(x,y)=1$. Let $\Pi$ be a randomized protocol that computes $F_{\mathrm{tot}}$ of eq. (5) with error at most $1/3$ on every input, with $CC(\Pi)<b$, and set $\delta=1/(10^{22}c)$. Then for every distribution $\mu$ supported on $\mathrm{dom}(F)$ there is a randomized protocol $\Pi_\mu$ for $F$ with
--   $$CC(\Pi_\mu)\le CC(\Pi)+1,\qquad \mathrm{err}_\mu(\Pi_\mu)\le\frac12-\frac\delta3 .$$
--
--   This is the distributional heart of Theorem 4.1; the minimax principle and error reduction then give a worst-case protocol.
--
--   **Formalization Note** The paper reaches (6) under $CC(\Pi)<R(F)$ with $R(F)\le n+1\le b$; the argument uses this only through $CC(\Pi)<b$. The property of $V$ is the conclusion of Section 3.1 (padded certificates).
--
--   Differences from the source:
--   - generalization: inputs in {0,1}^n → arbitrary finite input types X, Y; reason: {0,1}^n is a finite type, so the statement specializes
--   - generalization: CC(Π) < R(F) with R(F) ≤ n + 1 ≤ b → CC(Π) < b; reason: the argument uses only CC(Π) < b; the printed chain implies it
--   - generalization: c = ⌈K_E log² b⌉, the extractor of Lemma 2.3 and the padded certificate predicate of Section 3.1 → any c ≥ 1, any E with linear surjective fixed-seed maps that is a strong (2b, 10⁻¹²)-seeded extractor, and any V with both valid and invalid certificates on D_c pairs; reason: these are the only properties used; the paper's choices satisfy them
-- source:
--   Le Gall, Improved Separations between Quantum and Classical Communication Complexity of Total Functions, arXiv:2609.16726 (held version, sha256 970e1476…), proof of Theorem 4.1, "Fixing a distribution µ", (6), p.8; established pp.8–10

import Mathlib
import Definitions.Def_QCSepTotal_IsStrongExtractor
import Definitions.Def_QCSepTotal_LookupExperiment

namespace QCSepTotal

/-- **Proof of Theorem 4.1, claim (6)** (F. Le Gall, *Improved Separations between Quantum and Classical Communication Complexity of Total Functions*, arXiv:2609.16726 (held version, sha256 970e1476…), p.8; established pp.8–10).
Let `Π` be a `1/3`-error randomized protocol for `Ftot` (eq. (5)) with `CC(Π) < b`, built with
`c ≥ 1`, `b ≥ 40`, an extractor `E` with linear surjective fixed-seed maps that is a strong
`(2b, 10⁻¹²)`-seeded extractor, and a certificate predicate `V` that has both valid and invalid
certificates for every pair with `D_c(x, y) = 1`. Set `δ = 1/(10²² c)`. For each distribution
`µ` supported on `dom(F)` there is a protocol `Π_µ` for `F` with
`CC(Π_µ) ≤ CC(Π) + 1` and `err_µ(Π_µ) ≤ 1/2 − δ/3`.

**Formalization Note.** The paper reaches (6) under "`CC(Π) < R(F)`" with `R(F) ≤ n + 1 ≤ b`;
the proof uses this only through `CC(Π) < b`, which is the hypothesis here. The property of `V`
is the conclusion of Section 3.1 (padded certificates). -/
theorem theorem_4_1_eq_6 {X Y : Type} [Fintype X] [Fintype Y] (F : PartialFn X Y) (c b : ℕ)
    (hc : 1 ≤ c) (hb : 40 ≤ b)
    (E : (Fin c → ZMod 2) → (Fin (4 * b) → ZMod 2) →ₗ[ZMod 2] (Fin b → ZMod 2))
    (hEsurj : ∀ ℓ, Function.Surjective (E ℓ))
    (hEext : IsStrongExtractor (fun u ℓ => E ℓ u) (2 * (b : ℝ)) (1 / 10 ^ 12))
    (Vc : (Fin c → X) → (Fin c → Y) → (Fin b → ZMod 2) → Bool)
    (hV : ∀ x y, Dc F x y = true → (∃ p, Vc x y p = true) ∧ (∃ p, Vc x y p = false))
    (P : RandProtocol ((Fin c → X) × (Fin (4 * b) → ZMod 2)) ((Fin c → Y) × (Fin (4 * b) → ZMod 2)))
    (hP : P.Computes (total (Ftot F c b E Vc)) (1 / 3)) (hcost : P.cost < b)
    (μ : PMF (X × Y)) (hμ : ∀ p ∈ μ.support, (F p.1 p.2).isSome) :
    ∃ Pμ : RandProtocol X Y, Pμ.cost ≤ P.cost + 1 ∧ Pμ.distErr F μ ≤ 1 / 2 - deltaC c / 3 := by sorry

end QCSepTotal
