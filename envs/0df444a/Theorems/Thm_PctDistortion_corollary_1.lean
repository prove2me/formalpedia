-- Prove2me | Theorems.Thm_PctDistortion_corollary_1
-- name    : PctDistortion.corollary_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:43:06.239554+00:00
-- url     : https://prove2.me/theorems/54f9d7ca-e5c3-4546-83ad-df12cd43b578
-- title:
--   Corollary 1 — block payoffs (3) and the value of $G$ in terms of $\pi(a),\pi(b)$
-- statement:
--   Throughout, the standing assumptions of §4.1 hold: $\alpha\in[1/2,1)$, $H=(V_H,E_H)\in M_\alpha$ with $\hat\nu=\nu(\mathcal G^{ABC}_H)<1-2/s$ for an integer $s\ge 3$, $r\ge 1$ is an integer, $\ell=sr+1$, $C=\vec C^{\,r}_\ell$, and $G=C[P,H,\dots,H]$ with blocks $V_0=\{c_0,c^*\}$ and $V_i$ ($i\ne0$) copies of $H$.
--
--   Let $(a,b)$ be an equilibrium of the ABC game on $G$. Then:
--
--   1. Alice's expected payoff, conditional on Alice choosing block $i$ and Bob block $j$, is given by (3): $1$ if $i=j=0$; $\hat\nu$ if $i=j\ne0$; $-1$ if $i\in\{j+1,\dots,j+r\}$; $1$ otherwise;
--   2. the value of $\mathcal G^{ABC}_G$ is
--   $$\nu(\mathcal G^{ABC}_G)=\pi^{(a)}_0\pi^{(b)}_0+\sum_{i=1}^{\ell-1}\pi^{(a)}_i\pi^{(b)}_i\,\hat\nu+\sum_{i=0}^{\ell-1}\pi^{(a)}_i\Big(1-\pi^{(b)}_i-2\sum_{j=i-r}^{i-1}\pi^{(b)}_j\Big).$$
--
--   **Formalization Note** The conditional payoff in part 1 is stated for blocks with $\pi^{(a)}_i>0$ and $\pi^{(b)}_j>0$, where it is defined. Indices are modulo $\ell$.
--
--   Differences from the source:
--   - encoding: G = C[P, H, …, H] with blocks V_0 = {c₀, c*}, V_i copies of H → blowupG on Fin 2 ⊕ ({i : Fin ℓ // i ≠ 0} × V_H) with the block map; reason: a disjoint-union node type; same digraph
--   - reading: conditional expected payoff (3) for blocks i, j → stated for blocks with π(a)_i > 0 and π(b)_j > 0; reason: the conditional expectation is defined only there; the value formula of part 2 holds without the condition
--   - encoding: Σ_{j=i−r}^{i−1} π(b)_j with arithmetic mod ℓ → Σ_{t=1}^{r} π(b)_{i−t} in Fin ℓ; reason: the same terms
--   - encoding: ν = Alice's payoff under any equilibrium → Alice's maximin value (abcValue); reason: equal by the minimax theorem; the maximin value exists for every finite game
-- source:
--   Kizilkaya, Kalayci, Kempe, Micha, The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries, STOC 2027 submission (held version, sha256 fd779dd0…), Corollary 1, eq. (3), pp.13–14

import Mathlib
import Definitions.Def_PctDistortion_alphaMajority
import Definitions.Def_PctDistortion_abcValue
import Definitions.Def_PctDistortion_blowupG
import Definitions.Def_PctDistortion_reducedPayoff
import Definitions.Def_BlottoLP_Flow_ZeroSum

set_option autoImplicit false

namespace PctDistortion

/-- **Corollary 1** (block payoffs and the value of `G`). Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), Corollary 1, eq. (3), pp.13–14,
under the standing assumptions of §4.1, p.13: `H ∈ M_α` with `ν̂ = ν(G^ABC_H) < 1 − 2/s`
for an integer `s ≥ 3`, an integer `r ≥ 1`, `ℓ = s r + 1`, and `G = C[P, H, …, H]` (`blowupG`). If `(a, b)` is an equilibrium of the ABC game on `G`, then:
1. for blocks `i`, `j` chosen by Alice and Bob, Alice's expected payoff conditional on the blocks
   is (3): `1` if `i = j = 0`, `ν̂` if `i = j ≠ 0`, `−1` if `i ∈ {j + 1, …, j + r}`, `1` otherwise
   (`reducedPayoff`);
2. `ν(G^ABC_G) = π(a)_0 π(b)_0 + Σ_{i=1}^{ℓ−1} π(a)_i π(b)_i ν̂
   + Σ_{i=0}^{ℓ−1} π(a)_i (1 − π(b)_i − 2 Σ_{j=i−r}^{i−1} π(b)_j)`.

**Formalization Note.** The conditional payoff of part 1 is defined only when both blocks have
positive mass, `π(a)_i > 0` and `π(b)_j > 0`; it is stated there. Indices are modulo `ℓ`:
`Σ_{j=i−r}^{i−1} π(b)_j` is `Σ_{t=1}^{r} π(b)_{i−t}` with `Fin.ofNat ℓ t = t mod ℓ`. -/
theorem corollary_1 (α : ℝ) (hα₁ : 1 / 2 ≤ α) (hα₂ : α < 1) {VH : Type} [Fintype VH] [Nonempty VH]
    (H : Digraph VH) (hH : IsAlphaMajority α H) (s : ℕ) (hs : 3 ≤ s)
    (hν : abcValue H < 1 - 2 / (s : ℝ)) (r : ℕ) (hr : 1 ≤ r)
    (a b : BlowupVertex VH s r → ℝ)
    (hab : BlottoLP.Flow.IsNashEq (abcPayoff (blowupG H s r)) a b) :
    (∀ i j : Fin (s * r + 1), 0 < blockMass a i → 0 < blockMass b j →
      (∑ x, ∑ y, if block x = i ∧ block y = j then a x * b y * abcPayoff (blowupG H s r) x y
          else 0) / (blockMass a i * blockMass b j) = reducedPayoff (abcValue H) s r i j) ∧
    abcValue (blowupG H s r) =
      blockMass a 0 * blockMass b 0 +
        ∑ i ∈ Finset.univ.erase (0 : Fin (s * r + 1)),
          blockMass a i * blockMass b i * abcValue H +
        ∑ i : Fin (s * r + 1), blockMass a i * (1 - blockMass b i -
          2 * ∑ t ∈ Finset.Icc 1 r, blockMass b (i - Fin.ofNat (s * r + 1) t)) := by sorry

end PctDistortion
