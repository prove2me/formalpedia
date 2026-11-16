-- Prove2me | Theorems.Thm_PrivPCP_Supplement_theorem_5_5
-- name    : PrivPCP.Supplement.theorem_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T23:58:29.681686+00:00
-- url     : https://prove2.me/theorems/bfd42ab9-1073-47a2-8391-799d1b2fedf5
-- title:
--   Theorem 5.5 — private, robust circuit for zero-on-subcube with privacy $\rho^{k-1}/O(k)$ and $e^{-O(k^3+k^2\log(1/\rho))}/|\Psi|$, robustness $e^{-O(k)}$
-- statement:
--   Assume the setting of Lemma 5.4: a prime $q$, subgroups $S_i\le\mathbb F_q^\times$ of pairwise coprime orders $s_i$ with $\tfrac14\le s_i/s_j\le4$, subgroups $\Gamma_i\le S_i$ of distinct prime orders $h_i$, elements $\zeta_i$ with $H_i=\zeta_i\Gamma_i$ disjoint from $S_i$ (both invariant under $\Gamma_i$), grids $D=\prod_iH_i$ and $\Omega=\prod_iS_i$ with $|D|<N=|\Omega|$, $N\mid q-1$, $N<q\le N^6$, and, for $d_i=h_i+\lceil s_i/128\rceil$ and $v_i=7d_i+2h_i-2$, the margins $d_i-h_i\ge s_i/128$ and $v_i+1\le s_i/4$. Assume Conjecture 4.2 with product expansion constant $\rho=\rho(k,1/128,4)\in(0,1]$. Let $I=(\mathbb F_q,D,\Psi,C)$ be a $k$-dimensional zero-on-subcube instance over these parameters.
--
--   Then there is an absolute constant $C>0$ such that $f_I$ admits a private and robust circuit with auxiliary proofs (Definition 5.3) with respect to the encoding $\mathrm{Enc}(A)=\mathrm{ev}_\Omega(P)$, $P\sim\mathrm{Unif}(R_d(A))$, with the following properties:
--   1. honest correctness;
--   2. layerwise privacy at least $\rho^{k-1}/(Ck)$, and joint privacy under the measure $\mu$ of §6.3 at least
--   $$
--   \frac{\exp\bigl(-C(k^3+k^2\log(1/\rho))\bigr)}{\max(|\Psi|,1)};
--   $$
--   3. robustness parameters $\gamma,\epsilon_{\mathrm{in}},\epsilon_{\mathrm{lay}}$, each at least $e^{-Ck}$;
--   4. encoding length $N$, fan-in at most $CkN^{1/k}$ (for the gates and for the tester's queries), depth at most $Ck$, every layer's input block and every layer of at most $Ck^2N$ wires, at most $Ck^2N$ gates in total, and at most $C(N^{1/k}+k)$ tester queries for every fixing of the tester's randomness.
--
--   Its description can be constructed in time polynomial in $k$, $N$, $\mathrm{size}(I)$ and $\log q$: a single machine, on the description of $I$ and the side lengths $s_i$, halts within $(k+N+\mathrm{size}(I)+\log_2q+2)^K$ steps with the descriptions of the circuit and the tester, for a fixed $K$.
--
--   This is the circuit that the private PCP of Corollary 8.3 is assembled from: Lemma 8.1 reduces Circuit-SAT to zero-on-subcube, and Section 8 turns the private, robust circuit into a private PCP whose privacy is the joint privacy under $\mu$.
--
--   **Formalization Note** $C$, $K$ and the machine are fixed before $k$, $\rho$, $q$, the grids and $I$. Conjecture 4.2 enters as product expansion at constant $\rho$ for every arity $2\le r\le k$ at $\eta=1/128$, $\beta=4$ (published `PrivPCP.PunctRSPE`), as in the published goal. Gates and tester decisions are short programs (Turing machines with a parameter and a step budget); the tester is nonadaptive with integer weights. Tables $A:D\to\mathbb F_q$ are the inputs, laid out on the $N$ input wires by a bijection $\Omega\simeq[N]$. The honest prover and the laws of the random words are the construction's prescribed honest distributions (the prover sees only the input and earlier layers; each layer's random words are fresh); they are not part of the description.
--
--   Differences from the source:
--   - generalization: the setting of Lemma 5.4 (for some $n$) → its conclusion without the three clauses that involve $n$ ($n<|D|$, the upper bound on $N$, the hypercube-embedding bound); reason: Theorem 5.5's proof (Lemmas 6.1, 6.3, 7.1 and the parameter count) uses only the degree margins, the balance and coprimality of the $s_i$, $|D|<N<q$ and the subgroup conditions, so every instance of the source's setting satisfies the Lean hypotheses.
--   - encoding: $O(\cdot)$ and $\Omega(\cdot)$ bounds → one absolute constant $C>0$ fixed before $k,\rho,q$, the grids and $I$; reason: the reading of the published goal and Corollary 4.4.
--   - reading: joint privacy $\exp(-O(k^3+k^2\log(1/\rho)))/|\Psi|$ → $\exp(-C(k^3+k^2\log(1/\rho)))/\max(|\Psi|,1)$; reason: equal to the source's bound when $|\Psi|\ge1$; at $|\Psi|=0$ the source's quotient is undefined, the proof gives $\nu_k$ with the factor $|\Psi|+1$, and Lean's $x/0=0$ would make the clause vacuous.
--   - reading: Definition 5.3's unnamed gate operations and tester decisions → short programs (a Turing machine, a parameter string, a step budget), the tester nonadaptive with integer weights; reason: the description must be constructible in polynomial time, so gates must have short descriptions; §5.3's line-decoding gates are not short monomial lists, and its tester is nonadaptive with rational probabilities.
--   - reading: robustness (a) "for arbitrary auxiliary and random words" → for every $\epsilon_{\mathrm{lay}}$-faulty execution with arbitrary input, auxiliary and random words; reason: the stronger of the two readings, and the form Lemma 7.1 proves.
--   - reading: honest correctness "there exists a choice of distributions for the auxiliary words" → holds for the construction's prescribed honest prover and random-word laws, the same ones privacy refers to, with the prover at layer $\ell$ seeing only the input and earlier layers; reason: "The construction specifies their honest distributions"; the prescribed prover is one such choice, and the random words of layer $\ell$ are fresh.
--   - encoding: the encoding word on $\Omega$ → the $N$ input wires through a bijection $\Omega\simeq[N]$ given with the circuit; reason: the source fixes no ordering of $\Omega$; a relabeling of the input wires.
--   - encoding: "width and gate count $O(k^2N)$" → every layer's full input block and every layer's gate list have at most $Ck^2N$ wires, and the total number of gates is at most $Ck^2N$; reason: width bounds the wires of a layer, including its auxiliary and random words.
--   - encoding: "description constructed in time polynomial in $k,N,\mathrm{size}(I),\log q$" → a fixed oracle Turing machine run on the codes of $I$ and $(s_i)$ halts within $(k+N+\mathrm{size}(I)+\lfloor\log_2q\rfloor+2)^K$ steps with the codes of the circuit and the tester; reason: the base mission's machine model.
--   - encoding: $\mathrm{dist}(W_0,S)\le\epsilon N_0$ → some $c\in S$ at Hamming distance at most $\epsilon N_0$; reason: the distance to a finite set is a minimum.
-- source:
--   Bafna, Vyas, Private PCPs from Product Expansion, STOC 2027 submission manuscript (sha256 c2cac1e07fc4af8721f673867373fc5bd417aa65f45cf170c543568abcf1e47e), Theorem 5.5, p.33 (PDF p.35), with Definitions 5.1–5.3, pp.26–28, §5.2, p.30, Lemma 5.4, p.29, and §6.3, p.39

import Mathlib
import Definitions.Def_PrivPCP_Supplement_IsPrivRobust
import Definitions.Def_PrivPCP_Supplement_ZOSInstance
import Definitions.Def_PrivPCP_Supplement_encLaw
import Definitions.Def_PrivPCP_PunctRSPE
import Definitions.Def_PrivPCP_subgroupSet

set_option autoImplicit false

open QAlgorithms.Complexity QAdvFew.PoQOracle ZKSheafPCP

namespace PrivPCP.Supplement

/-- **Theorem 5.5 (Private, robust circuit for zero-on-subcube)** (Bafna, Vyas, *Private PCPs from
Product Expansion*, STOC 2027 submission manuscript (sha256 c2cac1e0…), Theorem 5.5, p.33, with
Definitions 5.1–5.3, pp.26–28, the encoding of §5.2, p.30, and the measure `µ` of §6.3, p.39). Assume
the setting of Lemma 5.4 and Conjecture 4.2 with product expansion constant `ρ = ρ(k, 1/128, 4)`.
Let `I = (𝔽_q, D, Ψ, C)` be a `k`-dimensional zero-on-subcube instance over these parameters. Then
`f_I` admits a private and robust circuit in the sense of Definition 5.3, with respect to the
encoding `Enc(A) = ev_Ω(P)`, `P ∼ Unif(R_d(A))`, `d_i = h_i + ⌈s_i/128⌉`, with:
1. honest correctness;
2. layerwise privacy at least `ρ^{k−1}/(Ck)` and joint privacy under `µ` at least
   `e^{−C(k³ + k² log(1/ρ))}/max(|Ψ|, 1)`;
3. robustness parameters `γ, ε_in, ε_lay`, each at least `e^{−Ck}`;
4. encoding length `N = |Ω|`, fan-in at most `C k N^{1/k}` (gates and tester), depth at most `C k`,
   every layer's input block and every layer of at most `C k² N` wires, at most `C k² N` gates, and at
   most `C(N^{1/k} + k)` tester queries for every fixing of its randomness.
Its description can be constructed in time polynomial in `k`, `N`, `size(I)`, `log q`: one machine
`Mach`, on the description of `I` and of the side lengths `s_i`, halts within
`(k + N + size(I) + log₂ q + 2)^K` steps with the description of the circuit and tester on its tape.

**Formalization Note** The `O(·)`, `Ω(·)` are one absolute constant `C`, and `K`, `Mach` are fixed,
before `k`, `ρ`, `q`, the grids and `I`. The setting of Lemma 5.4 is its conclusion
(`PrivPCP.lemma_5_4`) for the given `q`, `h_i`, `s_i`, `S_i`, `Γ_i`, `ζ_i`, without the clauses that
involve the circuit size `n` (`n < |D|`, the upper bound on `N`, the hypercube-embedding bound), which
Theorem 5.5 does not use. Conjecture 4.2 enters as product expansion at constant `ρ ∈ (0,1]` for every
arity `2 ⩽ r ⩽ k`, as in `PrivPCP.corollary_8_3`. The paper's bound `…/|Ψ|` is read as
`…/max(|Ψ|, 1)` (its proof gives `ν_k` with the factor `|Ψ| + 1`). Tables `A : D → 𝔽_q` are the
inputs; the encoding is laid out on the `N` input wires by a bijection `e : Ω ≃ [N]`. The honest prover
`P` and the random-word laws `R` are the construction's prescribed honest distributions of the
auxiliary and random words ("The construction specifies their honest distributions", p.27); they are
not part of the description. -/
theorem theorem_5_5 : ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, ∃ Mach : OTM,
    ∀ k : ℕ, 2 ≤ k → ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
    (∀ r : ℕ, 2 ≤ r → r ≤ k → PunctRSPE r (1 / 128) 4 ρ) →
    ∀ (q : ℕ) [Fact q.Prime] (h s : Fin k → ℕ) (S Γ : Fin k → Subgroup (ZMod q)ˣ)
      (ζ : Fin k → (ZMod q)ˣ),
    -- the setting of Lemma 5.4
    (∀ i, Nat.card (S i) = s i ∧ Nat.card (Γ i) = h i ∧ Γ i ≤ S i) →
    (∀ i, (1 / 128 : ℝ) * s i ≤ ((h i + ⌈(s i : ℝ) / 128⌉₊ : ℕ) : ℝ) - h i ∧
      ((7 * (h i + ⌈(s i : ℝ) / 128⌉₊) + 2 * h i - 2 + 1 : ℕ) : ℝ) ≤ (s i : ℝ) / 4) →
    ∏ i, h i < ∏ i, s i →
    (∀ i j, (1 / 4 : ℝ) ≤ (s i : ℝ) / s j ∧ (s i : ℝ) / s j ≤ 4) →
    (∀ i, (h i).Prime) → Function.Injective h → (∀ i j, i ≠ j → Nat.Coprime (s i) (s j)) →
    (∏ i, s i) ∣ q - 1 → ∏ i, s i < q → q ≤ (∏ i, s i) ^ 6 →
    (∀ i, ∀ γ ∈ Γ i, ζ i * γ ∉ S i) →
    (∀ i, ∀ γ ∈ Γ i, ∀ x : (ZMod q)ˣ,
      ((∃ γ' ∈ Γ i, x = ζ i * γ') → ∃ γ' ∈ Γ i, γ * x = ζ i * γ') ∧ (x ∈ S i → γ * x ∈ S i)) →
    -- a zero-on-subcube instance over these parameters
    ∀ I : ZOSInstance q k, I.IsValid → I.ζ = ζ → I.h = h →
      (∀ i, Subgroup.zpowers (I.ω i) = Γ i) →
    ∃ (Circ : LCircuit) (Tst : LTester)
      (e : ↥(Finset.univ.filter fun z : Fin k → ZMod q => ∀ i, z i ∈ subgroupSet (S i)) ≃
        Fin Circ.N0)
      (R : (ℓ : Fin Circ.L) → PMF (Fin (Circ.layer ℓ).rndLen → ZMod q))
      (P : (↥I.Dset → ZMod q) → Fin Circ.L → (Circ.Coord → ZMod q) → PMF (Circ.AuxIdx → ZMod q))
      (γ εin εlay : ℝ),
      -- the description, constructed in polynomial time
      Mach.result (fun _ => false) (tup [I.code, tup (List.ofFn fun i => binN (s i))])
          ((k + ∏ i, s i + I.code.length + Nat.log 2 q + 2) ^ K) ≠ none ∧
      Mach.output (fun _ => false) (tup [I.code, tup (List.ofFn fun i => binN (s i))])
          ((k + ∏ i, s i + I.code.length + Nat.log 2 q + 2) ^ K) = tup [Circ.code, Tst.code] ∧
      -- encoding length
      Circ.N0 = ∏ i, s i ∧
      -- 3. robustness parameters
      Real.exp (-(C * k)) ≤ γ ∧ Real.exp (-(C * k)) ≤ εin ∧ Real.exp (-(C * k)) ≤ εlay ∧
      -- 1–3: Definition 5.3 with fan-in, layerwise and joint privacy, robustness
      IsPrivRobust Circ Tst R P I.fI
        (fun A => (encLaw (fun i => h i + ⌈(s i : ℝ) / 128⌉₊) I.Dset
          (Finset.univ.filter fun z : Fin k → ZMod q => ∀ i, z i ∈ subgroupSet (S i)) A).map
            fun w j => w (e.symm j))
        (fun A => (fun w j => w (e.symm j)) '' encSet (fun i => h i + ⌈(s i : ℝ) / 128⌉₊) I.Dset
          (Finset.univ.filter fun z : Fin k → ZMod q => ∀ i, z i ∈ subgroupSet (S i)) A)
        (C * k * ((∏ i, s i : ℕ) : ℝ) ^ ((1 : ℝ) / k))
        (ρ ^ (k - 1) / (C * k))
        (Real.exp (-(C * ((k : ℝ) ^ 3 + (k : ℝ) ^ 2 * Real.log (1 / ρ)))) / max (I.Ψ.length : ℝ) 1)
        γ εin εlay ∧
      -- 4. depth, width, gate count, tester queries
      (Circ.L : ℝ) ≤ C * k ∧
      (∀ ℓ : Fin Circ.L, ((Circ.blockSet ℓ).ncard : ℝ) ≤ C * k ^ 2 * ((∏ i, s i : ℕ) : ℝ) ∧
        ((Circ.layer ℓ).gates.length : ℝ) ≤ C * k ^ 2 * ((∏ i, s i : ℕ) : ℝ)) ∧
      (Circ.gateCount : ℝ) ≤ C * k ^ 2 * ((∏ i, s i : ℕ) : ℝ) ∧
      (∀ t ∈ Tst.tests, 0 < t.weight →
        (t.queries.length : ℝ) ≤ C * (((∏ i, s i : ℕ) : ℝ) ^ ((1 : ℝ) / k) + k)) := by sorry

end PrivPCP.Supplement
