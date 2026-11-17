-- Prove2me | Theorems.Thm_QWildMatch_Supplement_theorem_4_1_reversible
-- name    : QWildMatch.Supplement.theorem_4_1_reversible
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:20:29.738238+00:00
-- url     : https://prove2.me/theorems/b35f3478-ed4f-4191-ab3b-f8ab25310869
-- title:
--   Theorem 4.1, last sentence (corrected: $|\Sigma|$ for $\log|\Sigma|$) — exact clean reversible fixed-start verifier with $O(m+r_+)$ queries
-- statement:
--   Let $\Sigma$ be a finite nonempty alphabet with an injective encoding $\mathrm{enc}:\Sigma\to\{0,1\}^{\lceil\log_2|\Sigma|\rceil}$. Let the cost table have integer values: $\mu(a,b),c_{\mathrm{del}}(a),c_{\mathrm{ins}}(b)\in\{0,1,\dots,W\}$ (the gap costs are positive, hence at least $1$). Let $T\in\Sigma^n$, $P\in(\Sigma\cup\{\star\})^m$, a threshold $k$, $r_+=\lfloor k/\alpha\rfloor$, $r_-=\lfloor k/\beta\rfloor$ and
--   $$b=\big\lceil\log_2\big((m+n)W+\lfloor k\rfloor+2\big)\big\rceil .$$
--
--   There are absolute constants $C>0$ and $c$ such that for all such data there is a reversible oracle circuit over $\{X,\mathrm{CNOT},\mathrm{Toffoli}\}$, chosen without knowledge of $T$, with a start register, one output bit and $a$ ancillas, such that:
--
--   1. for every text $T$, every start $s\le n$ and every bit $z$, with the text oracle $O_T$ as its black box it maps $|s\rangle|z\rangle|0^a\rangle$ **exactly** to $|s\rangle|z\oplus F(s)\rangle|0^a\rangle$, where $F(s)$ is the fixed-start predicate "some $T[s:e]$, $s\le e\le n$, has $\mathrm{ED}_\mu(P,T[s:e])\le k$";
--   2. it makes at most $C(m+r_+)$ calls to $O_T$ (plain, inverse or controlled);
--   3. it has at most $C(m+r_-+r_++b+|\Sigma|+2)^c$ elementary gates and at most as many ancillas.
--
--   This is the gate-level half of Theorem 4.1: the banded dynamic program can be run coherently, cleanly and without error, which is what amplitude amplification over starts (Corollary 4.2) needs. It is also the content of the last sentence of Theorem 1.1 ("the corresponding reversible verifier has polynomial gate complexity").
--
--   **Formalization Note** The page states the gate bound polynomial in $m,r_\pm,b,\log|\Sigma|$; that is false for arbitrary integer cost tables, and $|\Sigma|$ replaces $\log|\Sigma|$ (see below). The first three sentences of Theorem 4.1 are the published `QWildMatch.theorem_4_1` and are not restated.
--
--   Differences from the source:
--   - correction: polynomially many elementary gates and ancillas in m, r±, b, log |Σ| → gates and ancillas ≤ C·(m + r₋ + r₊ + b + |Σ| + 2)^c; reason: false as printed: with n = m = 1, P = [a], k = 0, c_del = c_ins = 2 and μ(a, ·) ∈ {0, 1} with μ(a, a) = 0 (W = 2, b constant), the test is μ(a, T[0]) = 0, an arbitrary Boolean function of T[0] with value 1 at a, so 2^{|Σ|−1} distinct tests; circuits of poly(log |Σ|) gates from {X, CNOT, Toffoli} plus the oracle on poly(log |Σ|) wires number only 2^{poly(log |Σ|)}. The hardwired cost table can be looked up with |Σ| equality tests, so |Σ| is the minimal correction
--   - encoding: O(m + r₊) text queries; polynomially many gates and ancillas → queryCount ≤ C·(m + r₊), gateCount and anc ≤ C·(m + r₋ + r₊ + b + |Σ| + 2)^c, with C, c absolute and quantified before the alphabet and every instance parameter; reason: the usual reading of O(·) and of polynomial bounds; the + 2 keeps the base at least 2 when every other parameter is 0
--   - encoding: integer costs bounded by W, bit width b = O(log((m + n)W + k + 2)) (§3, p.4) → every μ, c_del, c_ins value is a natural number at most W; b := ⌈log₂((m + n)W + ⌊k⌋₊ + 2)⌉; reason: b is Θ of the page's logarithm, so a polynomial in either is a polynomial in the other; k may stay real since costs are integers
--   - encoding: elementary gates → the gate set {X, CNOT, Toffoli} (published QuantumLTF.Membership.gatesRev); reason: classical reversible gates suffice for an exact clean reversible implementation, and every standard elementary gate set implements each of them exactly with O(1) gates, so the bound transfers
--   - encoding: text oracle O_T : |j, z⟩ ↦ |j, z ⊕ T[j]⟩, one query per (inverse) call → one black-box gate on ⌈log₂(n + 2)⌉ + ⌈log₂ |Σ|⌉ wires, symbols written through an injective enc, indices j ≥ n left unchanged; queryCount counts plain, inverse and controlled calls; reason: binary encodings of the index and symbol registers; the extra indices are never needed by a fixed-start test
--   - reading: the test (for a fixed start s) has an exact, clean reversible implementation → one circuit, independent of T, with the start s ≤ n in a register, mapping |s⟩|z⟩|0⟩ to |s⟩|z ⊕ FixedStart(s)⟩|0⟩ exactly for every T, s, z; reason: the theorem is titled 'Uniform fixed-start verifier' and Corollary 4.2 searches over starts with this circuit; the uniform circuit specializes to each fixed start
--   - generalization: cost table with μ(⋆, b) = 0 and μ(a, a) = 0 (§3, p.3) → any integer CostModel bounded by W, IsWildcardCost not assumed; reason: the banded DP and its reversible compilation use only nonnegativity of μ and positivity of the gaps; the §3 tables are special cases
--   - generalization: threshold k (implicitly k ≥ 0) → any real k; reason: for k < 0 no alignment has cost ≤ k, so the test is constantly false and the empty circuit implements it; the case k ≥ 0 is the source's
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu, Yue, Quantum Approximate Pattern Matching with Wildcards and Weighted Edits, STOC 2027 submission (file sha256 9e87a9dd…1f96), Theorem 4.1, last sentence, p.5 (integer costs and bit width: §3, p.4)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QWildMatch_Match
import Definitions.Def_QWildMatch_Supplement_textOracleGate
import Definitions.Def_QWildMatch_Supplement_IsExactCleanTest

namespace QWildMatch.Supplement

open QAlgorithms QWildMatch

/-- Theorem 4.1 (Uniform fixed-start verifier), last sentence, **corrected**, Zhao, Chen, Li, Kong, Peng,
Yu, Yue, STOC 2027 submission (file sha256 9e87a9dd…), p.5: for integer costs the fixed-start test has an
exact, clean reversible implementation using `O(m + r₊)` text queries and polynomially many elementary
gates and ancillas in `m`, `r±`, `b` and `|Σ|` (the page prints `log |Σ|`, which is false for arbitrary
cost tables; see the natural-language statement).

**Formalization Note** `C`, `c` are absolute: they precede the alphabet and every instance parameter.
Integer costs are the convention of §3, p.4: every `μ`, `c_del`, `c_ins` value is a natural number at most
`W`, and `b = ⌈log₂((m + n)W + ⌊k⌋₊ + 2)⌉`. The elementary gates are `gatesRev` = {X, CNOT, Toffoli}. The
symbol width is `w = ⌈log₂ |Σ|⌉` and `enc` is injective. The circuit may depend on `n`, `P`, the cost
table, `k`, `W` and `enc`, never on `T`; `queryCount` counts every call to `O_T` (plain, inverse or
controlled), `gateCount` the elementary gates, `anc` the wires beyond the start register and the output
bit. -/
theorem theorem_4_1_reversible :
    ∃ (C : ℝ) (c : ℕ), 0 < C ∧
    ∀ (Sym : Type) [Fintype Sym] [DecidableEq Sym] [Nonempty Sym]
      (enc : Sym → (Fin (Nat.clog 2 (Fintype.card Sym)) → Bool)), Function.Injective enc →
    ∀ (cm : CostModel Sym) (W : ℕ),
      (∀ a b, ∃ t : ℕ, cm.μ a b = t ∧ t ≤ W) →
      (∀ a, ∃ t : ℕ, cm.cdel a = t ∧ t ≤ W) →
      (∀ b, ∃ t : ℕ, cm.cins b = t ∧ t ≤ W) →
    ∀ (n : ℕ) (P : List (Option Sym)) (k : ℝ),
    ∃ (anc : ℕ) (circ : OracleCircuit QuantumLTF.Membership.gatesRev
        (fun _ : Fin 1 => idxBits n + Nat.clog 2 (Fintype.card Sym)) (idxBits n + 1 + anc)),
      IsExactCleanTest enc circ (fun T s => FixedStart cm P T k s) ∧
      (OracleCircuit.queryCount circ 0 : ℝ) ≤ C * ((P.length : ℝ) + (rPlus cm k : ℝ)) ∧
      (OracleCircuit.gateCount circ : ℝ) ≤
        C * ((P.length : ℝ) + (rMinus cm k : ℝ) + (rPlus cm k : ℝ) +
          (Nat.clog 2 ((P.length + n) * W + ⌊k⌋₊ + 2) : ℝ) + (Fintype.card Sym : ℝ) + 2) ^ c ∧
      (anc : ℝ) ≤
        C * ((P.length : ℝ) + (rMinus cm k : ℝ) + (rPlus cm k : ℝ) +
          (Nat.clog 2 ((P.length + n) * W + ⌊k⌋₊ + 2) : ℝ) + (Fintype.card Sym : ℝ) + 2) ^ c := by sorry

end QWildMatch.Supplement
