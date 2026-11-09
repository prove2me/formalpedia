-- Prove2me | Theorems.Thm_QCSepTotal_theorem_3_2
-- name    : QCSepTotal.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:38:54.97322+00:00
-- url     : https://prove2.me/theorems/f19f7c34-d08e-469d-b27b-3f040dc091f4
-- title:
--   Theorem 3.2 — $Q_{r+1}(F_{\mathrm{tot}})\le K\,(cq(\log c+1)+c+\ell_{\mathrm{test}})=\tilde O(q)$
-- statement:
--   There is an absolute constant $K$ with the following property. Let $F$ be a partial function on finite sets $X\times Y$ with $Q_r(F)\le q$, where $r\ge1$ and $q\ge1$. Let $c\ge1$, let $b_0\le b$, let $E_\ell:\mathbb F_2^{4b}\to\mathbb F_2^b$ ($\ell\in\mathbb F_2^c$) be any linear maps, and let $V_0(x,y;p)$ be a predicate on $b_0$-bit certificates for pairs of $c$-tuples such that
--
--   1. no certificate is valid when $D_c(x,y)=0$;
--   2. for the additive sharing in which Alice holds $x$ and her certificate share and Bob holds $y$ and his, there is a one-message test of length $\ell_{\mathrm{test}}$ in each direction (completeness $1$, soundness $1/64$).
--
--   Let $F_{\mathrm{tot}}$ be eq. (5) built from $E$ and the padded predicate $V(x,y;p)=V_0(x,y;p_1,\dots,p_{b_0})$. Then $F_{\mathrm{tot}}$ has a quantum protocol with at most $r+1$ messages, error at most $1/3$ on every input, and cost at most
--   $$K\bigl(c\,q\,(\log c+1)+c+\ell_{\mathrm{test}}\bigr).$$
--
--   With the test of Proposition 2.4 for the circuit of $D_c$, of size $O(cs)$, $\ell_{\mathrm{test}}=O(\log(cs))$, and the bound is the printed $O(cq\log c+c+\log s)=\tilde O(q)$, the quantum clause of Theorem 1.4.
--
--   **Formalization Note** The sharing $(x,p_A)$, $(y,p_B)$ is Proposition 2.4's additive sharing of $z=(x,y)$ with $z_A=(x,0)$, $z_B=(0,y)$. $\log c+1$ replaces $\log c$ so that the bound is meaningful at $c=1$.
--
--   Differences from the source:
--   - generalization: inputs in {0,1}^n → arbitrary finite input types X, Y; reason: {0,1}^n is a finite type, so the statement specializes
--   - generalization: Ftot of Section 3.1 (extractor of Lemma 2.3, V₀ of Proposition 2.4 for the D_c circuit); cost O(cq log c + c + log s) → any c ≥ 1, any linear fixed-seed maps E, any V₀ with no valid certificate off D_c and a one-message test of length len in each direction; cost K(cq(log₂ c + 1) + c + len); reason: Proposition 2.4 supplies such a V₀ with len = O(log(cs)), which gives the printed bound
--   - generalization: F has an r-message protocol of cost q → Q_r(F) ≤ q: at most r messages, cost at most q; reason: a protocol with exactly r messages and cost q qualifies
--   - reading: O(cq log c) → K c q (log₂ c + 1); reason: the O-bound read with log c + 1, which differs only at c = 1 where log c = 0
--   - encoding: the quantum protocol of the proof (private randomness, intermediate measurement of J, a classical last message) → the owned-qubit unitary model of QProtocol, start state |0…0⟩, one final computational-basis measurement by the last receiver; reason: randomness and measurements are simulated unitarily on ancillas (deferred measurement) and classical bits are sent as qubits, at no extra communication
-- source:
--   Le Gall, Improved Separations between Quantum and Classical Communication Complexity of Total Functions, arXiv:2609.16726 (held version, sha256 970e1476…), Theorem 3.2, p.7, with the cost O(cq log c + c + log s) of its proof, p.7

import Mathlib
import Definitions.Def_QCSepTotal_QProtocol
import Definitions.Def_QCSepTotal_Ftot
import Definitions.Def_QCSepTotal_IsOneMsgTest

namespace QCSepTotal

/-- **Theorem 3.2** (F. Le Gall, *Improved Separations between Quantum and Classical Communication Complexity of Total Functions*, arXiv:2609.16726 (held version, sha256 970e1476…), p.7): `Q_{r+1}(Ftot) = Õ(q)`, with the cost
`O(cq log c + c + log s)` computed in its proof (p.7).

Let `F` have a quantum protocol with at most `r ≥ 1` messages and cost `q ≥ 1`, and let `Ftot` be
eq. (5) with `c ≥ 1` copies, any extractor `E` with linear fixed-seed maps, and the padded
predicate `V(x, y; p) = V₀(x, y; p_{≤ b₀})` of Section 3.1, where `V₀` has no valid certificate on
pairs with `D_c(x, y) = 0` and admits a one-message test of length `len` in each direction for the
additive sharing in which Alice holds `x` and her certificate share and Bob holds `y` and his.
Then `Ftot` has a quantum protocol with at most `r + 1` messages and cost
`O(cq(log c + 1) + c + len)`, with an absolute constant chosen first.

**Formalization Note.** The test length is a parameter: Proposition 2.4 applied to the circuit
for `D_c`, of size `O(cs)`, gives `len = O(log(cs))`, the printed `O(c + log s)` term. The
sharing `(x, p_A)`, `(y, p_B)` is Proposition 2.4's additive sharing of `z = (x, y)` with
`z_A = (x, 0)`, `z_B = (0, y)`. `log c + 1` in place of `log c` keeps the bound meaningful at
`c = 1`. -/
theorem theorem_3_2 :
    ∃ K : ℝ, ∀ (X Y : Type) [Fintype X] [Fintype Y] (F : PartialFn X Y) (r q c b b₀ len : ℕ),
      1 ≤ r → 1 ≤ q → 1 ≤ c → HasQProtocol F r q → ∀ h : b₀ ≤ b,
      ∀ (E : (Fin c → ZMod 2) → (Fin (4 * b) → ZMod 2) →ₗ[ZMod 2] (Fin b → ZMod 2)),
      ∀ V₀ : (Fin c → X) × (Fin c → Y) → (Fin b₀ → ZMod 2) → Bool,
      (∀ x y, Dc F x y = false → ∀ p, V₀ (x, y) p = false) →
      IsOneMsgTest (fun (sA : (Fin c → X) × (Fin b₀ → ZMod 2)) (sB : (Fin c → Y) × (Fin b₀ → ZMod 2)) =>
        V₀ (sA.1, sB.1) (sA.2 + sB.2)) len →
      IsOneMsgTest (fun (sB : (Fin c → Y) × (Fin b₀ → ZMod 2)) (sA : (Fin c → X) × (Fin b₀ → ZMod 2)) =>
        V₀ (sA.1, sB.1) (sA.2 + sB.2)) len →
      HasQProtocol (total (Ftot F c b E (fun x y => padCert h V₀ (x, y)))) (r + 1)
        ⌊K * ((c : ℝ) * q * (Real.logb 2 c + 1) + c + len)⌋₊ := by sorry

end QCSepTotal
