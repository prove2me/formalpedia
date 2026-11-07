-- Prove2me | Theorems.Thm_PunctSketch_alt_collision
-- name    : PunctSketch.alt_collision
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:44:11.18994+00:00
-- url     : https://prove2.me/theorems/91beb29d-1975-491c-aa69-341179755d0c
-- title:
--   §5.3, p.20 — collision bound of the alternate fingerprint
-- statement:
--   Let $n\ge2$, let $Q>n^3$ be prime, and fix $G$, a set $E'$ of pairs, $|F|<k$ and $C$ disjoint from $F$, with different boundaries of $E$ and $E'$ at $C$. Let $\boldsymbol p_0,\dots,\boldsymbol p_c\in\mathbb F_Q^{c+k}$ be functions of $\Phi_F$ only, linearly independent and in the left kernel of $\Phi_F$, for each value of $\Phi_F$. For $\Phi\in\mathbb F_Q^{(c+k)\times n}$ uniform,
--   $$\Pr\Big[\forall t:\ \sum_{v\in C}\tilde f_F(v)_t=f_t\Big]\le\Big(\frac2Q\Big)^{c+1}\le n^{-c},$$
--   where $f_t$ is the fingerprint of $E'$ with the same $z_t$.
--
--   Differences from the source:
--   - generalization: Pr ≤ O(n^{−3(c+1)}) ≤ n^{−c}, through 2/(Q − 1) per coordinate → Pr ≤ (2/Q)^{c+1} ≤ n^{−c}; reason: the z_t(v) are uniform on all of 𝔽_Q, so Schwartz–Zippel gives 2/Q ≤ 2/(Q − 1); with Q = Θ(n³) this is the printed order
--   - reading: a suitably large prime Q = Θ(n³) → any prime Q > n³, with n ≥ 2; reason: fixes the unspecified constant of Θ; the primes in (n³, 2n³], which exist by Bertrand, are of that size
--   - reading: p.19 prints "F ⧵ V" for the subset → F ⊆ V; reason: a misprint
--   - encoding: vertices [n] = {1, …, n} → Fin n, zero-indexed; reason: Lean convention; same instances
-- source:
--   Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity, STOC 2027 submission (manuscript sha256 a630f88815653b5f1b35579cbfa2100b617a4d540f009489027b8c55f65e1a2c), §5.3, p.20 (PDF p.21)

import Mathlib
import Definitions.Def_PunctSketch_altFingerprint
import Definitions.Def_PunctSketch_puncturedBoundary
import Definitions.Def_PunctSketch_coinProb

namespace PunctSketch

/-- **Collision bound for the alternate fingerprint.** Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), §5.3, p.20: "by the Schwartz-Zippel lemma,
Pr[Σ_{v∈C} f̃_F(v)_t − f_t = 0] ≤ 2/(Q − 1) ≤ O(n^{−3}). Furthermore, since each p_t is linearly independent,
Pr[Σ_{v∈C} f̃_F(v) − f = 0] ≤ O(n^{−3(c+1)}) ≤ n^{−c}. As this probability holds for any fixing of Φ_F, it
holds unconditionally, as desired."

For `F`, `C`, `G`, `E′` with different boundaries, all fixed before `Φ`, and kernel vectors
`𝒑_0, …, 𝒑_c` that are linearly independent and a function of `Φ_F`, over uniform `Φ` the collision
probability is at most `(2/Q)^{c+1} ≤ n^{−c}`.

**Formalization Note.** The `z_t(v)` are uniform on all of `𝔽_Q`, so Schwartz–Zippel gives `2/Q`, at most the
printed `2/(Q − 1)`. `Q > n³` is the concrete form of `Q = Θ(n³)`. -/
theorem alt_collision {n c k Q : ℕ} [Fact Q.Prime] (hn : 2 ≤ n) (hQ : n ^ 3 < Q)
    (G : SimpleGraph (Fin n)) (E' : Set (Sym2 (Fin n))) (F C : Finset (Fin n)) (hF : F.card < k)
    (hC : Disjoint C F) (hE : G.edgeSet ∩ crossingPairs F C ≠ E' ∩ crossingPairs F C)
    (p : (Fin (c + k) → F → ZMod Q) → Fin (c + 1) → Fin (c + k) → ZMod Q)
    (hindep : ∀ ΦF, LinearIndependent (ZMod Q) (p ΦF))
    (hkernel : ∀ ΦF t z, ∑ i, p ΦF t i * ΦF i z = 0) :
    coinProb (fun Φ : Fin (c + k) → Fin n → ZMod Q =>
      ∀ t : Fin (c + 1),
        ∑ v ∈ C, altPunctured G Φ (p (fun i z => Φ i z) t) v =
          altBoundaryFp Φ (p (fun i z => Φ i z) t) F C E') ≤ (2 / (Q : ℝ)) ^ (c + 1) ∧
    (2 / (Q : ℝ)) ^ (c + 1) ≤ ((n : ℝ) ^ c)⁻¹ := by sorry

end PunctSketch
