-- Prove2me | Theorems.Thm_QCSepTotal_theorem_4_1
-- name    : QCSepTotal.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:41:55.34242+00:00
-- url     : https://prove2.me/theorems/a6df9d57-05af-4c76-9d47-40f1ef7e5f34
-- title:
--   Theorem 4.1 — every $1/3$-error protocol $\Pi$ for $F_{\mathrm{tot}}$ gives one for $F$ with $CC(\Pi')\le K c^2 CC(\Pi)=O(\log^4 b\cdot CC(\Pi))$
-- statement:
--   There is an absolute constant $K$ with the following property. Let $F$ be a partial function on finite sets $X\times Y$, let $c\ge1$ and $b\ge40$ with $R(F)\le b$, let the fixed-seed maps $E_\ell:\mathbb F_2^{4b}\to\mathbb F_2^b$ ($\ell\in\mathbb F_2^c$) be linear and surjective with $(u,\ell)\mapsto E_\ell(u)$ a strong $(2b,10^{-12})$-seeded extractor, and let $V$ be a certificate predicate with both valid and invalid certificates for every pair with $D_c(x,y)=1$. For every randomized protocol $\Pi$ computing $F_{\mathrm{tot}}$ of eq. (5) with error at most $1/3$, there is a randomized protocol $\Pi'$ computing $F$ with error at most $1/3$ and
--   $$CC(\Pi')\le K\,c^2\,CC(\Pi).$$
--
--   With the choice $c=\lceil K_E\log^2 b\rceil$ of Section 3.1 this is the printed bound $CC(\Pi')\le O(\log^4 b\cdot CC(\Pi))$. Minimizing over $\Pi$ gives Theorem 3.1, $R(F_{\mathrm{tot}})=\tilde\Omega(R(F))$, the randomized clause of Theorem 1.4.
--
--   **Formalization Note** The paper's $b\ge n+1\ge R(F)$ (p.7) is the hypothesis $R(F)\le b$.
--
--   Differences from the source:
--   - generalization: inputs in {0,1}^n → arbitrary finite input types X, Y; reason: {0,1}^n is a finite type, so the statement specializes
--   - generalization: c = ⌈K_E log² b⌉ and bound O(log⁴ b · CC(Π)) → any c ≥ 1 and bound K c² CC(Π) with K absolute; reason: the proof gives O(c² CC(Π)) (p.10); for c = ⌈K_E log² b⌉ and b ≥ 40, c² ≤ (K_E + 1)² log⁴ b
--   - generalization: b ≥ n + 1 ≥ R(F) → R(F) ≤ b; reason: the printed chain implies R(F) ≤ b, the only use
--   - generalization: the extractor of Lemma 2.3 (ε = 10⁻¹²) and the padded predicate of Proposition 2.4 → any E with linear surjective fixed-seed maps that is a strong (2b, 10⁻¹²)-seeded extractor, and any V with both valid and invalid certificates on D_c pairs; reason: these are the only properties the proof uses
--   - encoding: randomized protocols whose output is produced by a party (p.9: "Bob produces the output") → protocols whose output is the leaf label, with finite public and private coin types; reason: a party's final output can be sent as one more bit; for CC(Π) ≥ 1 the constant K absorbs it, and a cost-0 Π can compute Ftot only when dom(F) = ∅
-- source:
--   Le Gall, Improved Separations between Quantum and Classical Communication Complexity of Total Functions, arXiv:2609.16726 (held version, sha256 970e1476…), Theorem 4.1, p.7; proved pp.7–13

import Mathlib
import Definitions.Def_QCSepTotal_IsStrongExtractor
import Definitions.Def_QCSepTotal_RandProtocol
import Definitions.Def_QCSepTotal_Ftot

namespace QCSepTotal

/-- **Theorem 4.1** (F. Le Gall, *Improved Separations between Quantum and Classical Communication Complexity of Total Functions*, arXiv:2609.16726 (held version, sha256 970e1476…), p.7; proved pp.7–13). For every `1/3`-error
randomized protocol `Π` for `Ftot` there is a `1/3`-error randomized protocol `Π′` for `F`
such that `CC(Π′) ≤ O(log⁴ b · CC(Π))`.

Here `Ftot` is eq. (5) built from `c ≥ 1` copies, `b ≥ 40` with `R(F) ≤ b`, an extractor `E`
with linear surjective fixed-seed maps that is a strong `(2b, 10⁻¹²)`-seeded extractor, and a
certificate predicate `V` with both valid and invalid certificates on every pair with
`D_c(x, y) = 1`. The bound is `CC(Π′) ≤ K c² CC(Π)` with an absolute constant `K`, chosen first.

**Formalization Note.** The proof gives `O(c² CC(Π))` (p.10); with Section 3.1's
`c = ⌈K_E log² b⌉` this is the printed `O(log⁴ b · CC(Π))`. The paper's `b ≥ n + 1 ≥ R(F)` is the
hypothesis `R F ≤ b`. -/
theorem theorem_4_1 :
    ∃ K : ℝ, ∀ (X Y : Type) [Fintype X] [Fintype Y] (F : PartialFn X Y) (c b : ℕ),
      1 ≤ c → 40 ≤ b → R F ≤ b →
      ∀ (E : (Fin c → ZMod 2) → (Fin (4 * b) → ZMod 2) →ₗ[ZMod 2] (Fin b → ZMod 2)),
      (∀ ℓ, Function.Surjective (E ℓ)) →
      IsStrongExtractor (fun u ℓ => E ℓ u) (2 * (b : ℝ)) (1 / 10 ^ 12) →
      ∀ Vc : (Fin c → X) → (Fin c → Y) → (Fin b → ZMod 2) → Bool,
      (∀ x y, Dc F x y = true → (∃ p, Vc x y p = true) ∧ (∃ p, Vc x y p = false)) →
      ∀ P : RandProtocol ((Fin c → X) × (Fin (4 * b) → ZMod 2)) ((Fin c → Y) × (Fin (4 * b) → ZMod 2)),
      P.Computes (total (Ftot F c b E Vc)) (1 / 3) →
      ∃ P' : RandProtocol X Y, P'.Computes F (1 / 3) ∧ (P'.cost : ℝ) ≤ K * (c : ℝ) ^ 2 * P.cost := by sorry

end QCSepTotal
